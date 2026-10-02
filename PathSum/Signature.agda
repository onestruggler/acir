------------------------------------------------------------------------
-- Presentations of groups
--
-- Input signatures with Boolean constants (Amy, QPL 2018, definitions
-- 2.1 and 2.3)
--
-- Definition 2.1 gives a path-sum an input signature |x⟩ = x₁ ⋯ xₙ
-- "where each xᵢ is a (distinct) variable or Boolean constant", and
-- calls its operator a *partial* linear map: it is defined on the basis
-- states that match the constants.  PathSum.Base has variable inputs
-- only.  This package adds the constants, in four modules:
--
-- * Here: signatures, signed path-sums, their operator, definition 2.3
--   for them, and how constants 0 relate to the |0⟩-restrictions the
--   library already has.
-- * PathSum.Signature.Compose: compatibility of an output with an input
--   signature -- as the paper states it (syntactically), along every
--   path, and by the operator's range -- and definition 2.6 and
--   proposition 2.7 for signed path-sums, with counterexamples showing
--   that without compatibility the composite is neither the product nor
--   a function of the operators.
-- * PathSum.Signature.Clean: footnote 1.  Deciding compatibility
--   decides whether ancillas are left clean, and, through
--   PathSum.Hardness, whether a CNF formula is unsatisfiable.
-- * PathSum.Signature.WithX: preparing a wire in |1⟩ is preparing it in
--   |0⟩ and applying X, for circuits over {H, X, CNOT, R_k, R_k†}.
--
-- A signature gives each wire a slot, a variable or a constant b
-- (Slot, Signature).  The variable of wire i is the input variable xᵢ,
-- so the variables are distinct by construction.  A signed path-sum
-- σ ⊢ ξ (Signed) pairs a signature with a path-sum of PathSum.Base.
-- Its operator is the partial map of definition 2.1 extended by zero:
-- its entry from x to z is PathSum.Denotation's amp ξ x z when x agrees
-- with σ (Agrees: x carries every constant of σ), and 0 otherwise
-- (ampˢ, with ampˢ-in and ampˢ-out).  Extending by zero is composing
-- with the projection onto the span of the basis states σ admits; for
-- two path-sums with the same signature, equality of the extensions is
-- equality of the partial maps.  (Two partial maps with different
-- domains whose extensions agree -- both vanishing where only one is
-- defined -- are identified; definition 2.3 does not say which reading
-- it intends.)  Definition 2.3 is then _≋ˢ_, defined from ampˢ as
-- PathSum.Denotation's _≋_ is from amp, normalisations cross-
-- multiplied.  It is an equivalence (≋ˢ-refl, ≋ˢ-sym, ≋ˢ-trans), and
-- on the signature vars, every wire a variable, it is _≋_ (≋ˢ⇔≋):
-- PathSum.Base's path-sums are the signed ones without constants
-- (⌜_⌝).  Between two path-sums with one signature it compares the
-- columns the signature admits and nothing else (≋ˢ⇔on).
--
-- The polynomials of ξ may still mention the variable of a wire that σ
-- makes constant -- a freedom of the representation here; the paper's
-- path-sums have their constants written in -- and on the inputs σ
-- admits that variable takes the constant's value anyway.  inline σ ξ
-- writes the constants into the polynomials -- the path-sum as the
-- paper writes it, constants inline -- by PathSum.Polynomial.Bind's
-- simultaneous substitution.  Its value
-- at x is ξ's at pin σ x, x with σ's constants written over it
-- (eval-inline, outBit-inline, amp-inline), so it reads its input only
-- on the variable wires (amp-inline-vars), and it denotes the same
-- signed operator (inline-≋ˢ).  Two path-sums with one signature are
-- equivalent exactly when their inlined path-sums are equivalent as
-- path-sums of PathSum.Base (≋ˢ⇔inline).
--
-- Constants 0 are the library's |0⟩-restrictions.  zeros c puts the
-- constant 0 on the wires a mask c marks and variables elsewhere; it
-- admits exactly PathSum.Ancilla.Register's prepared inputs, so
-- ξ ≋⟨ c ⟩₀ ζ is (zeros c ⊢ ξ) ≋ˢ (zeros c ⊢ ζ) (≋⟨⟩₀⇔≋ˢ), and the
-- inlined path-sum is Register's set0ᶜ c ξ up to ≋ (inline-zeros).
-- Likewise PathSum.Ancilla's single ancilla i is the signature at i 0,
-- the constant 0 on wire i alone (Agrees-at, ≋[]₀⇔≋ˢ), and
-- PathSum.Ancillas's family a : Fin j → Fin n is the mask of a's image
-- (Clean⇔Agrees, ≋[]₀*⇔≋ˢ).  Constants 1 are new: none of those
-- modules prepares a wire in |1⟩, and a signature can (at i 1, whose
-- inlined path-sum reads ξ at x with xᵢ set to 1, pin-at).  The two are
-- related, for circuits, by an X gate (PathSum.Signature.WithX).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Signature (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (all?; any?)
open import Data.Product.Base using (∃; _,_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using
  (Dec; does; yes; no; ⌊_⌋; dec-true; dec-false)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin

open import PathSum.AmpLinear M₀ using (scale-comm)
open import PathSum.Ancilla M₀ using (_≋[_]₀_)
open import PathSum.Ancilla.Register M₀ using
  (Prepared; mask; set0ᶜ; amp-set0ᶜ; _≋⟨_⟩₀_)
open import PathSum.Ancillas M₀ using
  (Clean; _≋[_]₀*_; agree₀; amp-agree₀)
open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Compose.Properties M₀ using (hits-outBit; amp-≗ˣ)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ-cong; √2·-map; √2·-0ᴬ; scale; scale-map;
   scale-injective)
open import PathSum.Denotation M₀ using (Assign; amp; amp-≗; outBit; _≋_)
open import PathSum.Polynomial using (Poly; Var; x[_]; y[_]; κ; μ; eval)
open import PathSum.Polynomial.Bind using (bind; eval-bind; odd)
open import PathSum.Polynomial.Product using (eval-μᴾ)
open import PathSum.Polynomial.Properties using (valᵛ; eval-κ)

private
  variable
    n j k m k′ m′ k″ m″ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  -- Chaining equivalences of statements.

  infixr 5 _⟨⇔⟩_

  _⟨⇔⟩_ : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
  f ⟨⇔⟩ g = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
                (λ c → Equivalence.from f (Equivalence.from g c))


------------------------------------------------------------------------
-- Signatures

-- Each input wire is a variable or a Boolean constant.

data Slot : Set where
  var : Slot
  cst : Bool → Slot

Signature : ℕ → Set
Signature n = Fin n → Slot

-- Every wire a variable: PathSum.Base's path-sums.

vars : Signature n
vars _ = var

-- The bit a slot leaves of an input bit, and an input with σ's
-- constants written over it.

slot : Slot → Bool → Bool
slot var     c = c
slot (cst b) _ = b

pin : Signature n → Assign n → Assign n
pin σ x i = slot (σ i) (x i)

-- An input agrees with σ when it carries every constant of σ: writing
-- them over it changes nothing.

Agrees : Signature n → Assign n → Set
Agrees σ x = ∀ i → pin σ x i ≡ x i

agrees? : (σ : Signature n) (x : Assign n) → Dec (Agrees σ x)
agrees? σ x = all? (λ i → pin σ x i ≟ᵇ x i)

agrees : Signature n → Assign n → Bool
agrees σ x = does (agrees? σ x)

-- Every input agrees with vars; pin σ x agrees with σ; agreement reads
-- the input only through its values.

vars-agrees : (x : Assign n) → Agrees vars x
vars-agrees x i = refl

private
  slot-idem : ∀ s c → slot s (slot s c) ≡ slot s c
  slot-idem var     c = refl
  slot-idem (cst b) c = refl

pin-agrees : (σ : Signature n) (x : Assign n) → Agrees σ (pin σ x)
pin-agrees σ x i = slot-idem (σ i) (x i)

Agrees-≗ : (σ : Signature n) {x x′ : Assign n} → (∀ i → x i ≡ x′ i) →
           Agrees σ x → Agrees σ x′
Agrees-≗ σ h a i = trans (cong (slot (σ i)) (sym (h i))) (trans (a i) (h i))


------------------------------------------------------------------------
-- Signed path-sums and their operators

infix 5 _⊢_

record Signed (n k m : ℕ) : Set where
  constructor _⊢_
  field
    sig : Signature n
    ps  : PathSum n k m

open Signed public

-- The partial map of definition 2.1, extended by zero: the entry from
-- x to z, unnormalised.

ampˢ : Signed n k m → Assign n → Assign n → Amp
ampˢ ξ x z = if agrees (sig ξ) x then amp (ps ξ) x z else 0ᴬ

ampˢ-in : (ξ : Signed n k m) {x : Assign n} → Agrees (sig ξ) x →
          ∀ z → ampˢ ξ x z ≐ amp (ps ξ) x z
ampˢ-in ξ {x} a z i =
  cong (λ b → (if b then amp (ps ξ) x z else 0ᴬ) i)
       (dec-true (agrees? (sig ξ) x) a)

ampˢ-out : (ξ : Signed n k m) {x : Assign n} → ¬ Agrees (sig ξ) x →
           ∀ z → ampˢ ξ x z ≐ 0ᴬ
ampˢ-out ξ {x} na z i =
  cong (λ b → (if b then amp (ps ξ) x z else 0ᴬ) i)
       (dec-false (agrees? (sig ξ) x) na)

-- Only the values of the input and of the output are read.

ampˢ-≗ᶻ : (ξ : Signed n k m) (x : Assign n) {z z′ : Assign n} →
          (∀ i → z i ≡ z′ i) → ampˢ ξ x z ≐ ampˢ ξ x z′
ampˢ-≗ᶻ ξ x h = if-cong {p = agrees (sig ξ) x} refl (amp-≗ (ps ξ) x h)

ampˢ-≗ˣ : (ξ : Signed n k m) {x x′ : Assign n} → (∀ i → x i ≡ x′ i) →
          ∀ z → ampˢ ξ x z ≐ ampˢ ξ x′ z
ampˢ-≗ˣ ξ {x} {x′} h z = go (agrees? (sig ξ) x)
  where
  go : Dec (Agrees (sig ξ) x) → ampˢ ξ x z ≐ ampˢ ξ x′ z
  go (yes a) = ampˢ-in ξ a z ∙ amp-≗ˣ (ps ξ) h z
               ∙ ≐-sym (ampˢ-in ξ (Agrees-≗ (sig ξ) h a) z)
  go (no na) = ampˢ-out ξ na z
               ∙ ≐-sym (ampˢ-out ξ (λ a → na (Agrees-≗ (sig ξ)
                                              (λ i → sym (h i)) a)) z)

-- A path-sum of PathSum.Base is the signed path-sum with no constants.

⌜_⌝ : PathSum n k m → Signed n k m
⌜ ξ ⌝ = vars ⊢ ξ

ampˢ-⌜⌝ : (ξ : PathSum n k m) (x z : Assign n) → ampˢ ⌜ ξ ⌝ x z ≐ amp ξ x z
ampˢ-⌜⌝ ξ x z = ampˢ-in ⌜ ξ ⌝ (vars-agrees x) z


------------------------------------------------------------------------
-- Definition 2.3

infix 4 _≋ˢ_

_≋ˢ_ : Signed n k m → Signed n k′ m′ → Set
_≋ˢ_ {k = k} {k′ = k′} ξ ζ =
  ∀ x z → scale k′ (ampˢ ξ x z) ≐ scale k (ampˢ ζ x z)

≋ˢ-refl : {ξ : Signed n k m} → ξ ≋ˢ ξ
≋ˢ-refl _ _ _ = refl

≋ˢ-sym : {ξ : Signed n k m} {ζ : Signed n k′ m′} → ξ ≋ˢ ζ → ζ ≋ˢ ξ
≋ˢ-sym e x z i = sym (e x z i)

-- Transitivity cancels the middle normalisation, as for ≋.

≋ˢ-trans : {ξ : Signed n k m} {ζ : Signed n k′ m′} {χ : Signed n k″ m″} →
           ξ ≋ˢ ζ → ζ ≋ˢ χ → ξ ≋ˢ χ
≋ˢ-trans {k = k} {k′ = k′} {k″ = k″} {ξ = ξ} {ζ} {χ} e₁ e₂ x z =
  scale-injective k′ (scale k″ (ampˢ ξ x z)) (scale k (ampˢ χ x z))
    (scale-comm k′ k″ (ampˢ ξ x z)
     ∙ scale-map k″ (e₁ x z)
     ∙ scale-comm k″ k (ampˢ ζ x z)
     ∙ scale-map k (e₂ x z)
     ∙ scale-comm k k′ (ampˢ χ x z))

-- A power of √2 of nothing is nothing.

scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
scale-0ᴬ zero    i = refl
scale-0ᴬ (suc j) i = trans (√2·-map (scale-0ᴬ j) i) (√2·-0ᴬ i)

-- Between two path-sums with one signature, ≋ˢ compares the columns
-- the signature admits, and nothing else.

≋ˢ⇔on : (σ : Signature n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
        ((σ ⊢ ξ) ≋ˢ (σ ⊢ ζ)) ⇔
        (∀ x z → Agrees σ x → scale k′ (amp ξ x z) ≐ scale k (amp ζ x z))
≋ˢ⇔on {k = k} {k′ = k′} σ ξ ζ = mk⇔
  (λ e x z a → scale-map k′ (≐-sym (ampˢ-in (σ ⊢ ξ) a z)) ∙ e x z
               ∙ scale-map k (ampˢ-in (σ ⊢ ζ) a z))
  (λ h x z → back h x z (agrees? σ x))
  where
  back : (∀ x z → Agrees σ x → scale k′ (amp ξ x z) ≐ scale k (amp ζ x z)) →
         ∀ x z → Dec (Agrees σ x) →
         scale k′ (ampˢ (σ ⊢ ξ) x z) ≐ scale k (ampˢ (σ ⊢ ζ) x z)
  back h x z (yes a) = scale-map k′ (ampˢ-in (σ ⊢ ξ) a z) ∙ h x z a
                       ∙ scale-map k (≐-sym (ampˢ-in (σ ⊢ ζ) a z))
  back h x z (no na) = scale-map k′ (ampˢ-out (σ ⊢ ξ) na z) ∙ scale-0ᴬ k′
                       ∙ ≐-sym (scale-0ᴬ k)
                       ∙ scale-map k (≐-sym (ampˢ-out (σ ⊢ ζ) na z))

-- Without constants it is equivalence of path-sums.

≋ˢ⇔≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
       (⌜ ξ ⌝ ≋ˢ ⌜ ζ ⌝) ⇔ (ξ ≋ ζ)
≋ˢ⇔≋ ξ ζ = mk⇔
  (λ e x z → Equivalence.to (≋ˢ⇔on vars ξ ζ) e x z (vars-agrees x))
  (λ e → Equivalence.from (≋ˢ⇔on vars ξ ζ) (λ x z _ → e x z))


------------------------------------------------------------------------
-- The constants written inline

-- What each input variable becomes: itself on a variable wire, the
-- constant on a constant one.  Path variables stay.

slotᴾ : Slot → Fin n → Poly n m
slotᴾ var     i = μ x[ i ]
slotᴾ (cst b) i = κ [ b ]ᶻ

inlineᵛ : Signature n → Var n m → Poly n m
inlineᵛ σ x[ i ] = slotᴾ (σ i) i
inlineᵛ σ y[ j ] = μ y[ j ]

inline : Signature n → PathSum n k m → PathSum n k m
inline σ ξ =
  ⟨ bind (phase ξ) (inlineᵛ σ) , (λ w → bind (out ξ w) (inlineᵛ σ)) ⟩

-- Its polynomials take, at x, the values ξ's take at pin σ x.

eval-inline : (σ : Signature n) (P : Poly n m) (x : Assign n)
              (y : Assign m) →
              eval (bind P (inlineᵛ σ)) x y ≡ eval P (pin σ x) y
eval-inline {m = m} σ P x y = eval-bind P (inlineᵛ σ) x y (pin σ x) y value
  where
  pick : ∀ s i → eval (slotᴾ {m = m} s i) x y ≡ [ slot s (x i) ]ᶻ
  pick var     i = eval-μᴾ x[ i ] x y
  pick (cst b) i = eval-κ [ b ]ᶻ x y

  value : ∀ v → eval (inlineᵛ σ v) x y ≡ [ valᵛ v (pin σ x) y ]ᶻ
  value x[ i ] = pick (σ i) i
  value y[ j ] = eval-μᴾ y[ j ] x y

outBit-inline : (σ : Signature n) (ξ : PathSum n k m) (x : Assign n)
                (y : Assign m) (w : Fin n) →
                outBit (inline σ ξ) x y w ≡ outBit ξ (pin σ x) y w
outBit-inline σ ξ x y w = cong odd (eval-inline σ (out ξ w) x y)

amp-inline : (σ : Signature n) (ξ : PathSum n k m) (x z : Assign n) →
             amp (inline σ ξ) x z ≐ amp ξ (pin σ x) z
amp-inline σ ξ x z = Σᴮ-cong (λ y → if-cong
  (hits-outBit (inline σ ξ) ξ x (pin σ x) y y z
               (outBit-inline σ ξ x y))
  (zpow-≡ (eval-inline σ (phase ξ) x y)))

-- It reads its input on the variable wires only.

amp-inline-vars : (σ : Signature n) (ξ : PathSum n k m) {x x′ : Assign n} →
                  (∀ i → σ i ≡ var → x i ≡ x′ i) →
                  ∀ z → amp (inline σ ξ) x z ≐ amp (inline σ ξ) x′ z
amp-inline-vars σ ξ {x} {x′} h z =
  amp-inline σ ξ x z ∙ amp-≗ˣ ξ (λ i → keep (σ i) (h i)) z
  ∙ ≐-sym (amp-inline σ ξ x′ z)
  where
  keep : ∀ s {c c′} → (s ≡ var → c ≡ c′) → slot s c ≡ slot s c′
  keep var     h = h refl
  keep (cst b) h = refl

-- Writing the constants inline changes nothing σ admits.

inline-≋ˢ : (σ : Signature n) (ξ : PathSum n k m) →
            (σ ⊢ ξ) ≋ˢ (σ ⊢ inline σ ξ)
inline-≋ˢ {k = k} σ ξ = Equivalence.from (≋ˢ⇔on σ ξ (inline σ ξ))
  (λ x z a → scale-map k (amp-≗ˣ ξ (λ i → sym (a i)) z
                          ∙ ≐-sym (amp-inline σ ξ x z)))

-- Two path-sums with one signature are equivalent exactly when their
-- inlined path-sums are.

≋ˢ⇔inline : (σ : Signature n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
            ((σ ⊢ ξ) ≋ˢ (σ ⊢ ζ)) ⇔ (inline σ ξ ≋ inline σ ζ)
≋ˢ⇔inline {k = k} {k′ = k′} σ ξ ζ = mk⇔
  (λ e x z →
     scale-map k′ (amp-inline σ ξ x z)
     ∙ Equivalence.to (≋ˢ⇔on σ ξ ζ) e (pin σ x) z (pin-agrees σ x)
     ∙ scale-map k (≐-sym (amp-inline σ ζ x z)))
  (λ e → Equivalence.from (≋ˢ⇔on σ ξ ζ) λ x z a →
     scale-map k′ (amp-≗ˣ ξ (λ i → sym (a i)) z ∙ ≐-sym (amp-inline σ ξ x z))
     ∙ e x z
     ∙ scale-map k (amp-inline σ ζ x z ∙ amp-≗ˣ ζ a z))


------------------------------------------------------------------------
-- Constants 0: the |0⟩-restrictions of the library

-- The constant 0 on the wires the mask c marks, variables elsewhere.

zeros : (Fin n → Bool) → Signature n
zeros c i = if c i then cst false else var

private
  zeros-slot : ∀ b v → slot (if b then cst false else var) v ≡
                       (if b then false else v)
  zeros-slot true  v = refl
  zeros-slot false v = refl

  zeros-to : ∀ b v → (b ≡ true → v ≡ false) →
             slot (if b then cst false else var) v ≡ v
  zeros-to true  v h = sym (h refl)
  zeros-to false v h = refl

  zeros-from : ∀ b v → slot (if b then cst false else var) v ≡ v →
               b ≡ true → v ≡ false
  zeros-from true  v h refl = sym h
  zeros-from false v h ()

pin-zeros : (c : Fin n → Bool) (x : Assign n) →
            ∀ i → pin (zeros c) x i ≡ mask c x i
pin-zeros c x i = zeros-slot (c i) (x i)

-- zeros c admits exactly PathSum.Ancilla.Register's prepared inputs ...

Prepared⇔Agrees : (c : Fin n → Bool) (x : Assign n) →
                  Prepared c x ⇔ Agrees (zeros c) x
Prepared⇔Agrees c x = mk⇔
  (λ p i → zeros-to (c i) (x i) (p i))
  (λ a i → zeros-from (c i) (x i) (a i))

-- ... so Register's relation is ≋ˢ under zeros c ...

≋⟨⟩₀⇔≋ˢ : (c : Fin n → Bool) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
          (ξ ≋⟨ c ⟩₀ ζ) ⇔ ((zeros c ⊢ ξ) ≋ˢ (zeros c ⊢ ζ))
≋⟨⟩₀⇔≋ˢ c ξ ζ = mk⇔
  (λ h → Equivalence.from (≋ˢ⇔on (zeros c) ξ ζ)
           (λ x z a → h x z (Equivalence.from (Prepared⇔Agrees c x) a)))
  (λ e x z p → Equivalence.to (≋ˢ⇔on (zeros c) ξ ζ) e x z
                 (Equivalence.to (Prepared⇔Agrees c x) p))

-- ... and the path-sum with the constants inline is Register's set0ᶜ.

inline-zeros : (c : Fin n → Bool) (ξ : PathSum n k m) →
               inline (zeros c) ξ ≋ set0ᶜ c ξ
inline-zeros {k = k} c ξ x z = scale-map k
  (amp-inline (zeros c) ξ x z ∙ amp-≗ˣ ξ (pin-zeros c x) z
   ∙ ≐-sym (amp-set0ᶜ c ξ x z))

-- One constant b on the wire w, variables elsewhere.  It admits the
-- inputs whose bit on w is b, and writes b over that bit.

at : Fin n → Bool → Signature n
at w b i = if does (i Fin.≟ w) then cst b else var

Agrees-at : (w : Fin n) (b : Bool) (x : Assign n) →
            Agrees (at w b) x ⇔ (x w ≡ b)
Agrees-at w b x = mk⇔ to from
  where
  to : Agrees (at w b) x → x w ≡ b
  to a = sym (trans (sym (cong (λ d → slot (if d then cst b else var) (x w))
                               (dec-true (w Fin.≟ w) refl)))
                    (a w))

  from : x w ≡ b → Agrees (at w b) x
  from e i = go (i Fin.≟ w)
    where
    go : (d : Dec (i ≡ w)) → slot (if does d then cst b else var) (x i) ≡ x i
    go (yes refl) = sym e
    go (no _)     = refl

pin-at : (w : Fin n) (b : Bool) (x : Assign n) →
         ∀ i → pin (at w b) x i ≡ (x [ w ≔ b ]) i
pin-at w b x i = go (i Fin.≟ w)
  where
  go : (d : Dec (i ≡ w)) →
       slot (if does d then cst b else var) (x i) ≡ (if ⌊ d ⌋ then b else x i)
  go (yes _) = refl
  go (no _)  = refl

-- PathSum.Ancilla's single ancilla i is the constant 0 on wire i.

≋[]₀⇔≋ˢ : (i : Fin n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
          (ξ ≋[ i ]₀ ζ) ⇔ ((at i false ⊢ ξ) ≋ˢ (at i false ⊢ ζ))
≋[]₀⇔≋ˢ i ξ ζ = mk⇔
  (λ h → Equivalence.from (≋ˢ⇔on (at i false) ξ ζ)
           (λ x z a → h x z (Equivalence.to (Agrees-at i false x) a)))
  (λ e x z x₀ → Equivalence.to (≋ˢ⇔on (at i false) ξ ζ) e x z
                  (Equivalence.from (Agrees-at i false x) x₀))

-- PathSum.Ancillas's family a is the mask of a's image.

image : (Fin j → Fin n) → (Fin n → Bool)
image a w = does (any? (λ i → a i Fin.≟ w))

private
  does-true : {A : Set} (d : Dec A) → does d ≡ true → A
  does-true (yes a) _ = a
  does-true (no _)  ()

Clean⇔Prepared : (a : Fin j → Fin n) (x : Assign n) →
                 Clean a x ⇔ Prepared (image a) x
Clean⇔Prepared a x = mk⇔
  (λ cl w e → reach (does-true (any? (λ i → a i Fin.≟ w)) e) cl)
  (λ p i → p (a i) (dec-true (any? (λ i′ → a i′ Fin.≟ a i)) (i , refl)))
  where
  reach : ∀ {w} → ∃ (λ i → a i ≡ w) → Clean a x → x w ≡ false
  reach (i , refl) cl = cl i

Clean⇔Agrees : (a : Fin j → Fin n) (x : Assign n) →
               Clean a x ⇔ Agrees (zeros (image a)) x
Clean⇔Agrees a x = Clean⇔Prepared a x ⟨⇔⟩ Prepared⇔Agrees (image a) x

≋[]₀*⇔≋ˢ : (a : Fin j → Fin n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
           (ξ ≋[ a ]₀* ζ) ⇔
           ((zeros (image a) ⊢ ξ) ≋ˢ (zeros (image a) ⊢ ζ))
≋[]₀*⇔≋ˢ a ξ ζ = mk⇔
  (λ h → Equivalence.from (≋ˢ⇔on (zeros (image a)) ξ ζ)
           (λ x z ag → amp-agree₀ h x z
                         (Equivalence.from (Clean⇔Agrees a x) ag)))
  (λ e → agree₀ λ x z cl → Equivalence.to (≋ˢ⇔on (zeros (image a)) ξ ζ)
                             e x z (Equivalence.to (Clean⇔Agrees a x) cl))
