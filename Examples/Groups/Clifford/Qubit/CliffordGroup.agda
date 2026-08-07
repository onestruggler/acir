------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group modulo scalars (p = 2), written CMS n, as a
-- concrete group and as a non-split extension of Sp(2n,2) by the *plain*
-- Pauli group:
--
--     1 ─→ Pauli n ─→ CMS n ─→ Sp(2n, 2) ─→ 1.
--
-- The kernel is the phaseless Pauli group Pauli n = (ℤ/2 × ℤ/2)ⁿ — the
-- bundle +ₚ-group of Pauli.Semantics, with no phase attached.  The ℤ/4
-- phase of SignedPauli never appears there.  It appears one level down,
-- as the model deciding when two Clifford *words* (over the gate
-- generators Gen n) denote the same element of CMS n:
--
--     w ≈ᶜ v   ⟺   ∀ x → cact w x ≡ cact v x,
--
-- with x ranging over P4 n = ℤ/4 × Pauli n.
--
-- The phase is not optional in that role.  Conjugation by a Pauli is
-- symplectically trivial — that is proj-kills-incl below — so on
-- phaseless Paulis every incl P would act as the identity and
-- incl-injective would be false; what separates two Paulis is the phase
-- ι (sform P Q) they attach.  ℤ/2 signs would not do either, since
-- S X S⁻¹ = i X Z produces a genuine i.  Quotienting words by ≈ᶜ
-- therefore kills exactly the global scalars, whence the name:
-- CMS n = C(n)/⟨ω⟩.  The exact Clifford group C(n) is the scalar layer
-- above, in Qubit.ExactExtension.
--
-- Composition is word concatenation (cact (w • v) = cact w ∘ cact v); the
-- monoid laws are near-definitional.  Inverses use the P4-order of each
-- generator (S⁴ = H⁴ = CZ⁴ = 1 on P4).
--
-- The two maps of the extension are
--
--   * incl P = pauliWord P, the circuit X^a Z^b conjugating by P.  Its
--     P4-action is (s , Q) ↦ (s + ι (sform P Q) , Q): the phaseless Pauli
--     is fixed and the phase moves by the symplectic form.
--   * proj w = ⟦ w ⟧, the phaseless (symplectic) action of w.
--
-- Exactness at the middle is the substantive direction: a Clifford acting
-- trivially on the phaseless Paulis attaches only a phase φ; because
-- cact w is a P4-homomorphism φ is additive, because every Pauli has
-- order 2 it factors as ι ∘ g, and nondegeneracy of sform realises g as
-- sform v — so w is conjugation by v.  This is where non-splitness lives:
-- nothing here provides a section of proj.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.CliffordGroup where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Relation.Nullary.Decidable using (from-yes)
open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMonoid ; IsSemigroup ; IsMagma)
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; _↑)

open import Examples.Groups.Clifford.Qubit.SignedPauli using (P4Carrier)
open import Examples.Groups.Clifford.Qubit.CliffordAction using (cact)
open import Examples.Groups.Clifford.Qubit.CliffordAut using (g4-id)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Equality: equal action on P4

infix 4 _≈ᶜ_
_≈ᶜ_ : ∀ {n} → Word (Gen n) → Word (Gen n) → Set
_≈ᶜ_ {n} w v = (x : P4Carrier n) → cact w x ≡ cact v x

≈ᶜ-refl : {w : Word (Gen n)} → w ≈ᶜ w
≈ᶜ-refl x = Eq.refl

≈ᶜ-sym : {w v : Word (Gen n)} → w ≈ᶜ v → v ≈ᶜ w
≈ᶜ-sym w≈v x = Eq.sym (w≈v x)

≈ᶜ-trans : {w v u : Word (Gen n)} → w ≈ᶜ v → v ≈ᶜ u → w ≈ᶜ u
≈ᶜ-trans w≈v v≈u x = Eq.trans (w≈v x) (v≈u x)

≈ᶜ-isEquivalence : ∀ {n} → IsEquivalence (_≈ᶜ_ {n})
≈ᶜ-isEquivalence = record
  { refl  = λ {w}          → ≈ᶜ-refl {w = w}
  ; sym   = λ {w} {v}      → ≈ᶜ-sym {w = w} {v = v}
  ; trans = λ {w} {v} {u}  → ≈ᶜ-trans {w = w} {v = v} {u = u}
  }

------------------------------------------------------------------------
-- Monoid structure: concatenation of Clifford words
--
-- cact (w • v) = cact w ∘ cact v (word-act), so the magma/semigroup/monoid
-- laws all hold pointwise by computation.

∙-congᶜ : {w w' v v' : Word (Gen n)} → w ≈ᶜ w' → v ≈ᶜ v' → (w • v) ≈ᶜ (w' • v')
∙-congᶜ {w = w} {w'} {v} {v'} w≈w' v≈v' x =
  Eq.trans (Eq.cong (cact w) (v≈v' x)) (w≈w' (cact v' x))

assocᶜ : (w v u : Word (Gen n)) → ((w • v) • u) ≈ᶜ (w • (v • u))
assocᶜ w v u x = Eq.refl

identityˡᶜ : (w : Word (Gen n)) → (ε • w) ≈ᶜ w
identityˡᶜ w x = Eq.refl

identityʳᶜ : (w : Word (Gen n)) → (w • ε) ≈ᶜ w
identityʳᶜ w x = Eq.refl

isMonoidᶜ : ∀ {n} → IsMonoid (_≈ᶜ_ {n}) _•_ ε
isMonoidᶜ {n} = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = ≈ᶜ-isEquivalence {n}
      ; ∙-cong        = λ {w} {w'} {v} {v'} → ∙-congᶜ {n} {w} {w'} {v} {v'}
      }
    ; assoc = assocᶜ
    }
  ; identity = identityˡᶜ , identityʳᶜ
  }
  where open import Data.Product using (_,_)

CMS-monoid : ℕ → Monoid 0ℓ 0ℓ
CMS-monoid n = record { isMonoid = isMonoidᶜ {n} }

------------------------------------------------------------------------
-- Inverses: reverse the word and cube each generator (g³ = g⁻¹ on P4)

infix 8 _⁻¹ᶜ
_⁻¹ᶜ : Word (Gen n) → Word (Gen n)
[ g ]ʷ  ⁻¹ᶜ = [ g ]ʷ • [ g ]ʷ • [ g ]ʷ
ε       ⁻¹ᶜ = ε
(w • v) ⁻¹ᶜ = (v ⁻¹ᶜ) • (w ⁻¹ᶜ)

-- cact (w⁻¹ᶜ) cancels cact w on the left (using g4-id at generators).
invˡ-lemma : (w : Word (Gen n)) (x : P4Carrier n) → cact (w ⁻¹ᶜ) (cact w x) ≡ x
invˡ-lemma [ g ]ʷ  x = g4-id g x
invˡ-lemma ε       x = Eq.refl
invˡ-lemma (w • v) x =
  Eq.trans (Eq.cong (cact (v ⁻¹ᶜ)) (invˡ-lemma w (cact v x))) (invˡ-lemma v x)

invʳ-lemma : (w : Word (Gen n)) (x : P4Carrier n) → cact w (cact (w ⁻¹ᶜ) x) ≡ x
invʳ-lemma [ g ]ʷ  x = g4-id g x
invʳ-lemma ε       x = Eq.refl
invʳ-lemma (w • v) x =
  Eq.trans (Eq.cong (cact w) (invʳ-lemma v (cact (w ⁻¹ᶜ) x))) (invʳ-lemma w x)

⁻¹-congᶜ : {w v : Word (Gen n)} → w ≈ᶜ v → (w ⁻¹ᶜ) ≈ᶜ (v ⁻¹ᶜ)
⁻¹-congᶜ {w = w} {v} w≈v x =
  Eq.trans (Eq.cong (cact (w ⁻¹ᶜ)) (Eq.sym step1)) (invˡ-lemma w (cact (v ⁻¹ᶜ) x))
  where
  step1 : cact w (cact (v ⁻¹ᶜ) x) ≡ x
  step1 = Eq.trans (w≈v (cact (v ⁻¹ᶜ) x)) (invʳ-lemma v x)

------------------------------------------------------------------------
-- The Clifford group

open import Algebra.Bundles using (Group)
open import Algebra.Structures using (IsGroup)
open import Data.Product using (_,_)

isGroupᶜ : ∀ {n} → IsGroup (_≈ᶜ_ {n}) _•_ ε _⁻¹ᶜ
isGroupᶜ {n} = record
  { isMonoid = isMonoidᶜ {n}
  ; inverse  = (λ w → invˡ-lemma w) , (λ w → invʳ-lemma w)
  ; ⁻¹-cong  = λ {w} {v} → ⁻¹-congᶜ {w = w} {v}
  }

CMS-group : ℕ → Group 0ℓ 0ℓ
CMS-group n = record { isGroup = isGroupᶜ {n} }

------------------------------------------------------------------------
-- Shifting a Clifford word up one wire

open import Data.Product using (proj₁ ; proj₂ ; ∃-syntax)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Notations
open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; sform ; sform1)
open import Examples.Groups.Clifford.Qubit.SignedPauli using (Φ ; ι ; ι-+)
open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime using (X ; Z)
open import Examples.Groups.Clifford.Qubit.Selinger.Action using (cact-X↓ ; cact-Z↓)

-- cact w ↑ leaves the new wire 0 alone and runs cact w on the tail: the
-- phase δ (g ↥) and the action actg (g ↥) both ignore the head.
cact-↑ : (w : Word (Gen n)) (s : Φ) (q : Pauli1) (qs : Pauli n) →
         cact (w ↑) (s , q ∷ qs)
         ≡ (proj₁ (cact w (s , qs)) , q ∷ proj₂ (cact w (s , qs)))
cact-↑ [ g ]ʷ  s q qs = Eq.refl
cact-↑ ε       s q qs = Eq.refl
cact-↑ (w • v) s q qs =
  Eq.trans (Eq.cong (cact (w ↑)) (cact-↑ v s q qs))
           (cact-↑ w (proj₁ (cact v (s , qs))) q (proj₂ (cact v (s , qs))))

------------------------------------------------------------------------
-- Pauli words
--
-- The Clifford word realising conjugation by a Pauli operator: on each
-- wire, X^a Z^b built from the derived words X = HSSH and Z = SS.

-- One wire.  Conjugating by X^a Z^b multiplies by (-1)^{sform1 (a,b) -},
-- i.e. X reads off the Z-exponent and Z the X-exponent.
xz : ℤ ₚ → ℤ ₚ → Word (Gen (₁₊ n))
xz ₀ ₀ = ε
xz ₀ ₁ = Z
xz ₁ ₀ = X
xz ₁ ₁ = X • Z

-- sform1 against each of the four one-wire Pauli operators.  Both
-- arguments range over ℤ/2, so these are finite tables.
sform1-₀₀ : (c d : ℤ ₚ) → sform1 (₀ , ₀) (c , d) ≡ ₀
sform1-₀₀ ₀ ₀ = auto
sform1-₀₀ ₀ ₁ = auto
sform1-₀₀ ₁ ₀ = auto
sform1-₀₀ ₁ ₁ = auto

sform1-₀₁ : (c d : ℤ ₚ) → sform1 (₀ , ₁) (c , d) ≡ c
sform1-₀₁ ₀ ₀ = auto
sform1-₀₁ ₀ ₁ = auto
sform1-₀₁ ₁ ₀ = auto
sform1-₀₁ ₁ ₁ = auto

sform1-₁₀ : (c d : ℤ ₚ) → sform1 (₁ , ₀) (c , d) ≡ d
sform1-₁₀ ₀ ₀ = auto
sform1-₁₀ ₀ ₁ = auto
sform1-₁₀ ₁ ₀ = auto
sform1-₁₀ ₁ ₁ = auto

sform1-₁₁ : (c d : ℤ ₚ) → sform1 (₁ , ₁) (c , d) ≡ d + c
sform1-₁₁ ₀ ₀ = auto
sform1-₁₁ ₀ ₁ = auto
sform1-₁₁ ₁ ₀ = auto
sform1-₁₁ ₁ ₁ = auto

cact-xz : (a b : ℤ ₚ) (s : Φ) (c d : ℤ ₚ) (qs : Pauli n) →
          cact (xz a b) (s , (c , d) ∷ qs)
          ≡ (s + ι (sform1 (a , b) (c , d)) , (c , d) ∷ qs)
cact-xz ₀ ₀ s c d qs =
  Eq.cong (_, (c , d) ∷ qs)
    (Eq.trans (Eq.sym (+-identityʳ s))
              (Eq.cong (λ □ → s + ι □) (Eq.sym (sform1-₀₀ c d))))
cact-xz ₀ ₁ s c d qs =
  Eq.trans (cact-Z↓ s c d qs)
    (Eq.cong (λ □ → s + ι □ , (c , d) ∷ qs) (Eq.sym (sform1-₀₁ c d)))
cact-xz ₁ ₀ s c d qs =
  Eq.trans (cact-X↓ s c d qs)
    (Eq.cong (λ □ → s + ι □ , (c , d) ∷ qs) (Eq.sym (sform1-₁₀ c d)))
cact-xz ₁ ₁ s c d qs = begin
  cact (X • Z) (s , (c , d) ∷ qs)
    ≡⟨ Eq.cong (cact X) (cact-Z↓ s c d qs) ⟩
  cact X (s + ι c , (c , d) ∷ qs)
    ≡⟨ cact-X↓ (s + ι c) c d qs ⟩
  (s + ι c) + ι d , (c , d) ∷ qs
    ≡⟨ Eq.cong (_, (c , d) ∷ qs) step ⟩
  s + ι (sform1 (₁ , ₁) (c , d)) , (c , d) ∷ qs ∎
  where
  open Eq.≡-Reasoning
  step : (s + ι c) + ι d ≡ s + ι (sform1 (₁ , ₁) (c , d))
  step = begin
    (s + ι c) + ι d   ≡⟨ +-assoc s (ι c) (ι d) ⟩
    s + (ι c + ι d)   ≡⟨ Eq.cong (s +_) (+-comm (ι c) (ι d)) ⟩
    s + (ι d + ι c)   ≡⟨ Eq.cong (s +_) (Eq.sym (ι-+ d c)) ⟩
    s + ι (d + c)     ≡⟨ Eq.cong (λ □ → s + ι □) (Eq.sym (sform1-₁₁ c d)) ⟩
    s + ι (sform1 (₁ , ₁) (c , d)) ∎

-- A whole Pauli operator, wire by wire.
pauliWord : Pauli n → Word (Gen n)
pauliWord []             = ε
pauliWord ((a , b) ∷ ps) = xz a b • (pauliWord ps) ↑

-- Conjugation by P changes the phase by ι (sform P -) and fixes the
-- phaseless Pauli.
cact-pauliWord : (P : Pauli n) (s : Φ) (Q : Pauli n) →
                 cact (pauliWord P) (s , Q) ≡ (s + ι (sform P Q) , Q)
cact-pauliWord []             s []             =
  Eq.cong (_, []) (Eq.sym (+-identityʳ s))
cact-pauliWord ((a , b) ∷ ps) s ((c , d) ∷ qs) = begin
  cact (xz a b • (pauliWord ps) ↑) (s , (c , d) ∷ qs)
    ≡⟨ Eq.cong (cact (xz a b)) (cact-↑ (pauliWord ps) s (c , d) qs) ⟩
  cact (xz a b) (proj₁ (cact (pauliWord ps) (s , qs))
                , (c , d) ∷ proj₂ (cact (pauliWord ps) (s , qs)))
    ≡⟨ Eq.cong (λ y → cact (xz a b) (proj₁ y , (c , d) ∷ proj₂ y))
               (cact-pauliWord ps s qs) ⟩
  cact (xz a b) (s + ι (sform ps qs) , (c , d) ∷ qs)
    ≡⟨ cact-xz a b (s + ι (sform ps qs)) c d qs ⟩
  (s + ι (sform ps qs)) + ι (sform1 (a , b) (c , d)) , (c , d) ∷ qs
    ≡⟨ Eq.cong (_, (c , d) ∷ qs) step ⟩
  s + ι (sform1 (a , b) (c , d) + sform ps qs) , (c , d) ∷ qs ∎
  where
  open Eq.≡-Reasoning
  step : (s + ι (sform ps qs)) + ι (sform1 (a , b) (c , d))
       ≡ s + ι (sform1 (a , b) (c , d) + sform ps qs)
  step = begin
    (s + ι (sform ps qs)) + ι (sform1 (a , b) (c , d))
      ≡⟨ +-assoc s (ι (sform ps qs)) (ι (sform1 (a , b) (c , d))) ⟩
    s + (ι (sform ps qs) + ι (sform1 (a , b) (c , d)))
      ≡⟨ Eq.cong (s +_) (+-comm (ι (sform ps qs)) (ι (sform1 (a , b) (c , d)))) ⟩
    s + (ι (sform1 (a , b) (c , d)) + ι (sform ps qs))
      ≡⟨ Eq.cong (s +_) (Eq.sym (ι-+ (sform1 (a , b) (c , d)) (sform ps qs))) ⟩
    s + ι (sform1 (a , b) (c , d) + sform ps qs) ∎

------------------------------------------------------------------------
-- Bilinearity and nondegeneracy of sform

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (_+ₚ_ ; _+₁_ ; pIₙ ; pX ; pZ ; pI ; +ₚ-group ; +ₚ-identityˡ)
open import Examples.Groups.Clifford.Qubit.SignedPauli using (+-swap-middle)
open import Algebra.Properties.Ring (+-*-ring p-2) using (-‿+-comm)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

sform1-+ˡ : (p p' q : Pauli1) → sform1 (p +₁ p') q ≡ sform1 p q + sform1 p' q
sform1-+ˡ (a , b) (a' , b') (c , d) = begin
  (- (a + a')) * d + c * (b + b')
    ≡⟨ Eq.cong₂ _+_ (Eq.cong (_* d) (Eq.sym (-‿+-comm a a')))
                    (*-distribˡ-+ c b b') ⟩
  ((- a) + (- a')) * d + (c * b + c * b')
    ≡⟨ Eq.cong (_+ (c * b + c * b')) (*-distribʳ-+ d (- a) (- a')) ⟩
  ((- a) * d + (- a') * d) + (c * b + c * b')
    ≡⟨ +-swap-middle ((- a) * d) ((- a') * d) (c * b) (c * b') ⟩
  ((- a) * d + c * b) + ((- a') * d + c * b') ∎
  where open Eq.≡-Reasoning

sform-+ˡ : (P P' Q : Pauli n) → sform (P +ₚ P') Q ≡ sform P Q + sform P' Q
sform-+ˡ []       []         []       = Eq.sym (+-identityʳ ₀)
sform-+ˡ (p ∷ ps) (p' ∷ ps') (q ∷ qs) = begin
  sform1 (p +₁ p') q + sform (ps +ₚ ps') qs
    ≡⟨ Eq.cong₂ _+_ (sform1-+ˡ p p' q) (sform-+ˡ ps ps' qs) ⟩
  (sform1 p q + sform1 p' q) + (sform ps qs + sform ps' qs)
    ≡⟨ +-swap-middle (sform1 p q) (sform1 p' q) (sform ps qs) (sform ps' qs) ⟩
  (sform1 p q + sform ps qs) + (sform1 p' q + sform ps' qs) ∎
  where open Eq.≡-Reasoning

-- sform vanishes on the identity, on either side.
sform1-pIʳ : (p : Pauli1) → sform1 p pI ≡ ₀
sform1-pIʳ (₀ , ₀) = auto
sform1-pIʳ (₀ , ₁) = auto
sform1-pIʳ (₁ , ₀) = auto
sform1-pIʳ (₁ , ₁) = auto

sform-pIʳ : (P : Pauli n) → sform P pIₙ ≡ ₀
sform-pIʳ []       = Eq.refl
sform-pIʳ (p ∷ ps) =
  Eq.trans (Eq.cong₂ _+_ (sform1-pIʳ p) (sform-pIʳ ps)) (+-identityʳ ₀)

sform-pIˡ : (Q : Pauli n) → sform pIₙ Q ≡ ₀
sform-pIˡ []             = Eq.refl
sform-pIˡ ((c , d) ∷ qs) =
  Eq.trans (Eq.cong₂ _+_ (sform1-₀₀ c d) (sform-pIˡ qs)) (+-identityʳ ₀)

-- Probing with X and Z on wire 0 reads off the two exponents of the head.
sform-probeX : (p : Pauli1) (ps : Pauli n) →
               sform (p ∷ ps) (pX ∷ pIₙ) ≡ proj₂ p
sform-probeX (₀ , ₀) ps = Eq.trans (Eq.cong (₀ +_) (sform-pIʳ ps)) (+-identityʳ ₀)
sform-probeX (₀ , ₁) ps = Eq.trans (Eq.cong (₁ +_) (sform-pIʳ ps)) (+-identityʳ ₁)
sform-probeX (₁ , ₀) ps = Eq.trans (Eq.cong (₀ +_) (sform-pIʳ ps)) (+-identityʳ ₀)
sform-probeX (₁ , ₁) ps = Eq.trans (Eq.cong (₁ +_) (sform-pIʳ ps)) (+-identityʳ ₁)

sform-probeZ : (p : Pauli1) (ps : Pauli n) →
               sform (p ∷ ps) (pZ ∷ pIₙ) ≡ proj₁ p
sform-probeZ (₀ , ₀) ps = Eq.trans (Eq.cong (₀ +_) (sform-pIʳ ps)) (+-identityʳ ₀)
sform-probeZ (₀ , ₁) ps = Eq.trans (Eq.cong (₀ +_) (sform-pIʳ ps)) (+-identityʳ ₀)
sform-probeZ (₁ , ₀) ps = Eq.trans (Eq.cong (₁ +_) (sform-pIʳ ps)) (+-identityʳ ₁)
sform-probeZ (₁ , ₁) ps = Eq.trans (Eq.cong (₁ +_) (sform-pIʳ ps)) (+-identityʳ ₁)

-- Nondegeneracy: sform separates points.  Probing with X₀ and Z₀ pins the
-- head, probing with pI ∷ qs recurses into the tail.
sform-separates : (P P' : Pauli n) → (∀ Q → sform P Q ≡ sform P' Q) → P ≡ P'
sform-separates []       []         hyp = Eq.refl
sform-separates (p ∷ ps) (p' ∷ ps') hyp =
  Eq.cong₂ _∷_ head-eq (sform-separates ps ps' tail-hyp)
  where
  head-eq : p ≡ p'
  head-eq = ≡×≡⇒≡
    ( Eq.trans (Eq.sym (sform-probeZ p ps))
        (Eq.trans (hyp (pZ ∷ pIₙ)) (sform-probeZ p' ps'))
    , Eq.trans (Eq.sym (sform-probeX p ps))
        (Eq.trans (hyp (pX ∷ pIₙ)) (sform-probeX p' ps')) )
  tail-hyp : ∀ qs → sform ps qs ≡ sform ps' qs
  tail-hyp qs = begin
    sform ps qs                    ≡⟨ Eq.sym (+-identityˡ (sform ps qs)) ⟩
    ₀ + sform ps qs                ≡⟨ Eq.cong (_+ sform ps qs) (Eq.sym (sform1-pIʳ' p)) ⟩
    sform1 p pI + sform ps qs      ≡⟨ hyp (pI ∷ qs) ⟩
    sform1 p' pI + sform ps' qs    ≡⟨ Eq.cong (_+ sform ps' qs) (sform1-pIʳ' p') ⟩
    ₀ + sform ps' qs               ≡⟨ +-identityˡ (sform ps' qs) ⟩
    sform ps' qs ∎
    where
    open Eq.≡-Reasoning
    sform1-pIʳ' = sform1-pIʳ

-- ι : ℤ/2 → ℤ/4 is injective, so it reflects phase equalities.
ι-injective : {x y : ℤ ₚ} → ι x ≡ ι y → x ≡ y
ι-injective {₀} {₀} _  = Eq.refl
ι-injective {₀} {₁} ()
ι-injective {₁} {₀} ()
ι-injective {₁} {₁} _  = Eq.refl

------------------------------------------------------------------------
-- The two maps of the extension
--
--   incl : Pauli n → CMS n       conjugation by a Pauli operator,
--   proj : CMS n → Sp(2n,2)      the induced phaseless action.

open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
  using (_≈ˢ_ ; _∘ˢ_ ; εˢ ; Sp-group)
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧)
open import Examples.Groups.Symplectic.Surjectivity p-2 p-prime using (surj-nf)

incl : Pauli n → Word (Gen n)
incl = pauliWord

proj : Word (Gen n) → Sem.Symplectic n
proj = ⟦_⟧

-- The Pauli component of the P4-action is the phaseless action of w.
cact-proj₂ : (w : Word (Gen n)) (x : P4Carrier n) →
             proj₂ (cact w x) ≡ ap ⟦ w ⟧ (proj₂ x)
cact-proj₂ [ g ]ʷ  (s , P) = Eq.refl
cact-proj₂ ε       (s , P) = Eq.refl
cact-proj₂ (w • v) x =
  Eq.trans (cact-proj₂ w (cact v x)) (Eq.cong (ap ⟦ w ⟧) (cact-proj₂ v x))

------------------------------------------------------------------------
-- incl is a group homomorphism

module _ {n : ℕ} where

  private
    module MN = MonoidMorphisms (Group.rawMonoid (+ₚ-group n))
                                (Group.rawMonoid (CMS-group n))

  -- Conjugation phases add, so incl turns +ₚ into word concatenation.
  incl-∙ : (P P' : Pauli n) → incl (P +ₚ P') ≈ᶜ (incl P • incl P')
  incl-∙ P P' (s , Q) = begin
    cact (pauliWord (P +ₚ P')) (s , Q)
      ≡⟨ cact-pauliWord (P +ₚ P') s Q ⟩
    s + ι (sform (P +ₚ P') Q) , Q
      ≡⟨ Eq.cong (λ □ → s + ι □ , Q) (sform-+ˡ P P' Q) ⟩
    s + ι (sform P Q + sform P' Q) , Q
      ≡⟨ Eq.cong (λ □ → s + □ , Q) (ι-+ (sform P Q) (sform P' Q)) ⟩
    s + (ι (sform P Q) + ι (sform P' Q)) , Q
      ≡⟨ Eq.cong (λ □ → s + □ , Q) (+-comm (ι (sform P Q)) (ι (sform P' Q))) ⟩
    s + (ι (sform P' Q) + ι (sform P Q)) , Q
      ≡⟨ Eq.cong (_, Q) (Eq.sym (+-assoc s (ι (sform P' Q)) (ι (sform P Q)))) ⟩
    (s + ι (sform P' Q)) + ι (sform P Q) , Q
      ≡⟨ Eq.sym (Eq.trans (Eq.cong (cact (pauliWord P)) (cact-pauliWord P' s Q))
                          (cact-pauliWord P (s + ι (sform P' Q)) Q)) ⟩
    cact (pauliWord P • pauliWord P') (s , Q) ∎
    where open Eq.≡-Reasoning

  -- The identity Pauli conjugates trivially.
  incl-ε : incl (pIₙ {n}) ≈ᶜ ε
  incl-ε (s , Q) = begin
    cact (pauliWord pIₙ) (s , Q)   ≡⟨ cact-pauliWord pIₙ s Q ⟩
    s + ι (sform pIₙ Q) , Q        ≡⟨ Eq.cong (λ □ → s + ι □ , Q) (sform-pIˡ Q) ⟩
    s + ₀ , Q                      ≡⟨ Eq.cong (_, Q) (+-identityʳ s) ⟩
    s , Q ∎
    where open Eq.≡-Reasoning

  incl-mon : MN.IsMonoidHomomorphism incl
  incl-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ { Eq.refl _ → Eq.refl } }
      ; homo              = incl-∙
      }
    ; ε-homo = incl-ε
    }

  -- Two Pauli operators conjugating alike are equal: their phase
  -- functions ι ∘ sform agree, ι is injective, and sform is nondegenerate.
  incl-injective : {P P' : Pauli n} → incl P ≈ᶜ incl P' → P ≡ P'
  incl-injective {P} {P'} h = sform-separates P P' claim
    where
    claim : ∀ Q → sform P Q ≡ sform P' Q
    claim Q = ι-injective
      (Eq.trans (Eq.sym (+-identityˡ (ι (sform P Q))))
        (Eq.trans phase-eq (+-identityˡ (ι (sform P' Q)))))
      where
      -- Run both conjugations from phase ₀ and compare the phases.
      phase-eq : ₀ + ι (sform P Q) ≡ ₀ + ι (sform P' Q)
      phase-eq = Eq.cong proj₁
        (Eq.trans (Eq.sym (cact-pauliWord P ₀ Q))
          (Eq.trans (h (₀ , Q)) (cact-pauliWord P' ₀ Q)))

------------------------------------------------------------------------
-- proj is a group homomorphism, and is onto

-- Well-defined: equal P4-action ⇒ equal phaseless action.
proj-cong : {w v : Word (Gen n)} → w ≈ᶜ v → proj w ≈ˢ proj v
proj-cong {w = w} {v} w≈v P =
  Eq.trans (Eq.sym (cact-proj₂ w (₀ , P)))
    (Eq.trans (Eq.cong proj₂ (w≈v (₀ , P))) (cact-proj₂ v (₀ , P)))

module _ {n : ℕ} where

  private
    module MP = MonoidMorphisms (Group.rawMonoid (CMS-group n))
                                (Group.rawMonoid (Sp-group n))

  -- ⟦ w • v ⟧ = ⟦ w ⟧ ∘ˢ ⟦ v ⟧ and ⟦ ε ⟧ = εˢ hold definitionally.
  proj-mon : MP.IsMonoidHomomorphism proj
  proj-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ {w} {v} → proj-cong {n} {w} {v} }
      ; homo              = λ _ _ _ → Eq.refl
      }
    ; ε-homo = λ _ → Eq.refl
    }

  -- Every symplectic transformation is realised by a circuit.
  proj-surjective : (S : Sem.Symplectic n) → ∃[ w ] proj w ≈ˢ S
  proj-surjective = surj-nf

  -- Conjugation by a Pauli is invisible to the phaseless action.
  proj-kills-incl : (P : Pauli n) → proj (incl P) ≈ˢ εˢ
  proj-kills-incl P Q =
    Eq.trans (Eq.sym (cact-proj₂ (pauliWord P) (₀ , Q)))
             (Eq.cong proj₂ (cact-pauliWord P ₀ Q))

------------------------------------------------------------------------
-- Why CMS n cannot be built on phaseless Paulis
--
-- The tempting simplification is to identify Clifford words when they
-- agree on Pauli n rather than on P4 n.  That does not give CMS n but
-- Sp(2n, 2): the phaseless action of a Clifford *is* its symplectic map,
-- so the whole Pauli kernel collapses.  phaseless-blind says it — any
-- two Paulis conjugate alike phaselessly — and X₀≢Z₀ exhibits two that
-- must nevertheless stay apart, so incl-injective would be false at one
-- qubit and above.
--
-- One sign bit is not enough either, and the reason is worth recording,
-- since it is what pins the phase group at ℤ/4.  Clifford conjugation
-- does act faithfully on the *signed* Hermitian Paulis ±i^{ab}XᵃZᵇ, the
-- Aaronson-Gottesman tableau, which is only ℤ/2 × Pauli n.  But those do
-- not form a group — X · Z = -i·(iXZ) leaves the set — and the exactness
-- proof below needs a group: φ-+ derives additivity of the phase from
-- cact w being a homomorphism of P4.  Conversely the ± Pauli group
-- {± XᵃZᵇ} *is* a group but is not Clifford-stable, S X S⁻¹ = i XZ
-- escaping it.  ℤ/4 is the smallest phase group that is both.

phaseless-blind : (P P' : Pauli n) → proj (incl P) ≈ˢ proj (incl P')
phaseless-blind P P' Q =
  Eq.trans (proj-kills-incl P Q) (Eq.sym (proj-kills-incl P' Q))

X₀≢Z₀ : Eq._≢_ (pX ∷ pIₙ {n}) (pZ ∷ pIₙ {n})
X₀≢Z₀ ()

------------------------------------------------------------------------
-- Exactness at the middle: a Clifford in the kernel of proj is a Pauli
--
-- If w acts trivially on the phaseless Paulis then all it does is attach
-- a phase, cact w (s , Q) = (s + φ Q , Q).  Because cact w is a
-- homomorphism of P4, φ is additive; because 2·Q = 0, φ has order 2 and
-- so factors as ι ∘ g with g : Pauli n → ℤ/2 additive.  Nondegeneracy of
-- sform then realises g as sform v, and w agrees with conjugation by v.

open import Examples.Groups.Clifford.Qubit.SignedPauli using (γ ; γ-εˡ ; _·_)
-- CliffordAction's phase map ℤ/2 → ℤ/4 is renamed so that it does not
-- clash with `incl`, the inclusion of the extension above.
open import Examples.Groups.Clifford.Qubit.CliffordAction
  using (δ) renaming (incl to inclΦ)
open import Examples.Groups.Clifford.Qubit.CliffordAut using (cact-homo ; neg-id)
open import Examples.Groups.Clifford.Qubit.Selinger.Action using (cact-phase ; x+x)
open Symplectic using (gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥ ; S)
open Sem.Interpretation using (actg)

-- Generic cancellation in ℤ/m (both ℤ ₚ and Φ occur below; the modulus
-- is written ₂₊ m because the additive inverse needs it at least 2).
+-cancelˡ' : ∀ {m} (z x y : ℤ (₂₊ m)) → z + x ≡ z + y → x ≡ y
+-cancelˡ' z x y eq = begin
  x                 ≡⟨ Eq.sym (+-identityˡ x) ⟩
  ₀ + x             ≡⟨ Eq.cong (_+ x) (Eq.sym (+-inverseˡ z)) ⟩
  (- z + z) + x     ≡⟨ +-assoc (- z) z x ⟩
  - z + (z + x)     ≡⟨ Eq.cong (- z +_) eq ⟩
  - z + (z + y)     ≡⟨ Eq.sym (+-assoc (- z) z y) ⟩
  (- z + z) + y     ≡⟨ Eq.cong (_+ y) (+-inverseˡ z) ⟩
  ₀ + y             ≡⟨ +-identityˡ y ⟩
  y ∎
  where open Eq.≡-Reasoning

-- Every Pauli has order 2, and the generators fix the identity Pauli.
+ₚ-self : (P : Pauli n) → P +ₚ P ≡ pIₙ
+ₚ-self []            = Eq.refl
+ₚ-self ((a , b) ∷ ps) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ (x+x a , x+x b)) (+ₚ-self ps)

δ-pIₙ : (g : Gen n) → δ g pIₙ ≡ ₀
δ-pIₙ (gate₁ H-gate)  = Eq.cong ι (*-zeroˡ ₀)
δ-pIₙ (gate₁ S-gate)  = Eq.refl
δ-pIₙ (gate₂ CZ-gate) = Eq.cong ι (*-zeroˡ ₀)
δ-pIₙ (g ↥)           = δ-pIₙ g

actg-pIₙ : (g : Gen n) → actg g pIₙ ≡ pIₙ
actg-pIₙ (gate₁ H-gate)  = Eq.cong (_∷ pIₙ) (≡×≡⇒≡ (neg-id ₀ , Eq.refl))
actg-pIₙ (gate₁ S-gate)  = Eq.cong (_∷ pIₙ) (≡×≡⇒≡ (Eq.refl , +-identityʳ ₀))
actg-pIₙ (gate₂ CZ-gate) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ (Eq.refl , +-identityʳ ₀))
               (Eq.cong (_∷ pIₙ) (≡×≡⇒≡ (Eq.refl , +-identityʳ ₀)))
actg-pIₙ (g ↥)           = Eq.cong (_ ∷_) (actg-pIₙ g)

cact-pIₙ : (w : Word (Gen n)) → cact w (₀ , pIₙ) ≡ (₀ , pIₙ)
cact-pIₙ [ g ]ʷ  =
  Eq.cong₂ _,_ (Eq.trans (Eq.cong (₀ +_) (δ-pIₙ g)) (+-identityʳ ₀)) (actg-pIₙ g)
cact-pIₙ ε       = Eq.refl
cact-pIₙ (w • v) = Eq.trans (Eq.cong (cact w) (cact-pIₙ v)) (cact-pIₙ w)

-- Halving in ℤ/4: the order-2 elements are exactly ₀ and ₂ = ι ₁.
half : Φ → ℤ ₚ
half ₀ = ₀
half ₁ = ₀
half ₂ = ₁
half ₃ = ₀

ι-half : (z : Φ) → z + z ≡ ₀ → ι (half z) ≡ z
ι-half ₀ _  = Eq.refl
ι-half ₁ ()
ι-half ₂ _  = Eq.refl
ι-half ₃ ()

------------------------------------------------------------------------
-- Realising an additive functional as sform v
--
-- sform against the four one-wire basis probes (finite tables again).

sf-₀₀ : (α β : ℤ ₚ) → sform1 (α , β) (₀ , ₀) ≡ ₀
sf-₀₀ ₀ ₀ = auto
sf-₀₀ ₀ ₁ = auto
sf-₀₀ ₁ ₀ = auto
sf-₀₀ ₁ ₁ = auto

sf-₁₀ : (α β : ℤ ₚ) → sform1 (α , β) (₁ , ₀) ≡ β
sf-₁₀ ₀ ₀ = auto
sf-₁₀ ₀ ₁ = auto
sf-₁₀ ₁ ₀ = auto
sf-₁₀ ₁ ₁ = auto

sf-₀₁ : (α β : ℤ ₚ) → sform1 (α , β) (₀ , ₁) ≡ α
sf-₀₁ ₀ ₀ = auto
sf-₀₁ ₀ ₁ = auto
sf-₀₁ ₁ ₀ = auto
sf-₀₁ ₁ ₁ = auto

sf-₁₁ : (α β : ℤ ₚ) → sform1 (α , β) (₁ , ₁) ≡ α + β
sf-₁₁ ₀ ₀ = auto
sf-₁₁ ₀ ₁ = auto
sf-₁₁ ₁ ₀ = auto
sf-₁₁ ₁ ₁ = auto

-- An additive functional kills the identity.
additive-ε : (g : Pauli n → ℤ ₚ) →
             (∀ P P' → g (P +ₚ P') ≡ g P + g P') → g pIₙ ≡ ₀
additive-ε g g-+ = Eq.sym (+-cancelˡ' (g pIₙ) ₀ (g pIₙ)
  (Eq.trans (+-identityʳ (g pIₙ))
    (Eq.trans (Eq.cong g (Eq.sym (+ₚ-self pIₙ))) (g-+ pIₙ pIₙ))))

-- The vector representing g, read off the standard basis wire by wire:
-- the X-slot of wire i is g at Z on wire i, and vice versa.
dual : (Pauli n → ℤ ₚ) → Pauli n
dual {0}    g = []
dual {₁₊ m} g = (g (pZ ∷ pIₙ) , g (pX ∷ pIₙ)) ∷ dual (λ qs → g (pI ∷ qs))

dual-correct : (g : Pauli n → ℤ ₚ) →
               (g-+ : ∀ P P' → g (P +ₚ P') ≡ g P + g P') →
               (Q : Pauli n) → sform (dual g) Q ≡ g Q
dual-correct {0}    g g-+ []             = Eq.sym (additive-ε g g-+)
dual-correct {₁₊ m} g g-+ ((c , d) ∷ qs) = begin
  sform1 (α , β) (c , d) + sform (dual g') qs
    ≡⟨ Eq.cong (sform1 (α , β) (c , d) +_) (dual-correct g' g'-+ qs) ⟩
  sform1 (α , β) (c , d) + g (pI ∷ qs)
    ≡⟨ Eq.cong (_+ g (pI ∷ qs)) (head c d) ⟩
  g ((c , d) ∷ pIₙ) + g (pI ∷ qs)
    ≡⟨ Eq.sym (g-+ ((c , d) ∷ pIₙ) (pI ∷ qs)) ⟩
  g (((c , d) ∷ pIₙ) +ₚ (pI ∷ qs))
    ≡⟨ Eq.cong g split ⟩
  g ((c , d) ∷ qs) ∎
  where
  open Eq.≡-Reasoning
  α = g (pZ ∷ pIₙ)
  β = g (pX ∷ pIₙ)
  g' = λ qs → g (pI ∷ qs)
  g'-+ : ∀ ps ps' → g' (ps +ₚ ps') ≡ g' ps + g' ps'
  g'-+ ps ps' = g-+ (pI ∷ ps) (pI ∷ ps')

  split : ((c , d) ∷ pIₙ) +ₚ (pI ∷ qs) ≡ (c , d) ∷ qs
  split = Eq.cong₂ _∷_ (≡×≡⇒≡ (+-identityʳ c , +-identityʳ d)) (+ₚ-identityˡ qs)

  -- The (₁,₁) case is the only one needing additivity: X·Z on one wire.
  XZ-split : g ((₁ , ₁) ∷ pIₙ) ≡ α + β
  XZ-split = Eq.trans (Eq.cong g (Eq.sym pZ+pX)) (g-+ (pZ ∷ pIₙ) (pX ∷ pIₙ))
    where
    pZ+pX : (pZ ∷ pIₙ) +ₚ (pX ∷ pIₙ) ≡ (₁ , ₁) ∷ pIₙ
    pZ+pX = Eq.cong ((₁ , ₁) ∷_) (+ₚ-self pIₙ)

  head : (c d : ℤ ₚ) → sform1 (α , β) (c , d) ≡ g ((c , d) ∷ pIₙ)
  head ₀ ₀ = Eq.trans (sf-₀₀ α β) (Eq.sym (additive-ε g g-+))
  head ₁ ₀ = sf-₁₀ α β
  head ₀ ₁ = sf-₀₁ α β
  head ₁ ₁ = Eq.trans (sf-₁₁ α β) (Eq.sym XZ-split)

------------------------------------------------------------------------
-- A Clifford acting trivially on phaseless Paulis is a Pauli

module _ {n : ℕ} (w : Word (Gen n)) (triv : proj w ≈ˢ εˢ) where

  -- The phase w attaches, measured from zero phase.
  φ : Pauli n → Φ
  φ Q = proj₁ (cact w (₀ , Q))

  -- All w does is attach that phase.
  cact-triv : (s : Φ) (Q : Pauli n) → cact w (s , Q) ≡ (s + φ Q , Q)
  cact-triv s Q =
    Eq.cong₂ _,_ (cact-phase w s Q)
                 (Eq.trans (cact-proj₂ w (s , Q)) (triv Q))

  φ-pIₙ : φ pIₙ ≡ ₀
  φ-pIₙ = Eq.cong proj₁ (cact-pIₙ w)

  -- φ is additive: cact w is a homomorphism of P4, and the commutation
  -- cocycle γ contributes the same term on both sides, so it cancels.
  φ-+ : (P P' : Pauli n) → φ (P +ₚ P') ≡ φ P + φ P'
  φ-+ P P' = +-cancelˡ' (γ P P') _ _ step
    where
    open Eq.≡-Reasoning
    raw : ((₀ + ₀) + γ P P') + φ (P +ₚ P')
        ≡ ((₀ + φ P) + (₀ + φ P')) + γ P P'
    raw = Eq.cong proj₁
      (Eq.trans (Eq.sym (cact-triv ((₀ + ₀) + γ P P') (P +ₚ P')))
        (Eq.trans (cact-homo w (₀ , P) (₀ , P'))
                  (Eq.cong₂ _·_ (cact-triv ₀ P) (cact-triv ₀ P'))))
    step : γ P P' + φ (P +ₚ P') ≡ γ P P' + (φ P + φ P')
    step = begin
      γ P P' + φ (P +ₚ P')
        ≡⟨ Eq.cong (_+ φ (P +ₚ P'))
             (Eq.sym (Eq.trans (Eq.cong (_+ γ P P') (+-identityˡ ₀))
                               (+-identityˡ (γ P P')))) ⟩
      ((₀ + ₀) + γ P P') + φ (P +ₚ P')
        ≡⟨ raw ⟩
      ((₀ + φ P) + (₀ + φ P')) + γ P P'
        ≡⟨ Eq.cong₂ (λ x y → (x + y) + γ P P')
                    (+-identityˡ (φ P)) (+-identityˡ (φ P')) ⟩
      (φ P + φ P') + γ P P'
        ≡⟨ +-comm (φ P + φ P') (γ P P') ⟩
      γ P P' + (φ P + φ P') ∎

  -- Every Pauli has order 2, so φ does too, so it lands in the image of ι.
  φ-2 : (P : Pauli n) → φ P + φ P ≡ ₀
  φ-2 P = Eq.trans (Eq.sym (φ-+ P P)) (Eq.trans (Eq.cong φ (+ₚ-self P)) φ-pIₙ)

  gφ : Pauli n → ℤ ₚ
  gφ Q = half (φ Q)

  ι-gφ : (Q : Pauli n) → ι (gφ Q) ≡ φ Q
  ι-gφ Q = ι-half (φ Q) (φ-2 Q)

  gφ-+ : (P P' : Pauli n) → gφ (P +ₚ P') ≡ gφ P + gφ P'
  gφ-+ P P' = ι-injective
    (Eq.trans (ι-gφ (P +ₚ P'))
      (Eq.trans (φ-+ P P')
        (Eq.trans (Eq.cong₂ _+_ (Eq.sym (ι-gφ P)) (Eq.sym (ι-gφ P')))
                  (Eq.sym (ι-+ (gφ P) (gφ P'))))))

  -- The Pauli operator whose conjugation is w.
  ker-witness : Pauli n
  ker-witness = dual gφ

  ker-witness-correct : incl ker-witness ≈ᶜ w
  ker-witness-correct (s , Q) = begin
    cact (pauliWord (dual gφ)) (s , Q)
      ≡⟨ cact-pauliWord (dual gφ) s Q ⟩
    s + ι (sform (dual gφ) Q) , Q
      ≡⟨ Eq.cong (λ □ → s + ι □ , Q) (dual-correct gφ gφ-+ Q) ⟩
    s + ι (gφ Q) , Q
      ≡⟨ Eq.cong (λ □ → s + □ , Q) (ι-gφ Q) ⟩
    s + φ Q , Q
      ≡⟨ Eq.sym (cact-triv s Q) ⟩
    cact w (s , Q) ∎
    where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The Clifford group as a group extension
--
--     1 ─→ Pauli n ─→ CMS n ─→ Sp(2n, 2) ─→ 1

open import ForStdlib.Algebra.Construct.Extension using (Extension)

CMS-extension : (n : ℕ) → Extension (+ₚ-group n) (Sp-group n)
CMS-extension n = record
  { total           = CMS-group n
  ; incl            = incl
  ; proj            = proj
  ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                        (+ₚ-group n) (CMS-group n) incl-mon
  ; proj-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                        (CMS-group n) (Sp-group n) proj-mon
  ; incl-injective  = incl-injective
  ; proj-surjective = proj-surjective
  ; proj-kills-incl = proj-kills-incl
  ; ker⊆im-incl     = λ w triv → ker-witness w triv , ker-witness-correct w triv
  }

------------------------------------------------------------------------
-- The extension does not split: S² = Z
--
-- The phase gate S projects to a transvection of order 2 in Sp(2n,2),
-- but in the Clifford group it squares to the Pauli Z rather than to the
-- identity — so proj has no section sending that involution to an
-- involution.  This is the concrete obstruction that makes
-- CMS-extension a genuinely non-split extension, and the reason it
-- cannot be built with `semidirect` (which would force S² = 1).
--
-- It is also the semantic counterpart of corr (order-S) = Z₀, the one
-- nontrivial entry of the cocycle in Qubit.Presentation.

-- inclΦ a + inclΦ a = ι a: two ×1 phases make a ×2 phase.
incl-2 : (a : ℤ ₚ) → inclΦ a + inclΦ a ≡ ι a
incl-2 ₀ = auto
incl-2 ₁ = auto

S²=Z : ∀ {n} → (S • S) ≈ᶜ incl {₁₊ n} (pZ ∷ pIₙ)
S²=Z {n} (s , (a , b) ∷ ps) = Eq.trans lhs (Eq.sym rhs)
  where
  -- Z on wire 0 pairs with the X-exponent of the probe.
  probe : sform (pZ ∷ pIₙ) ((a , b) ∷ ps) ≡ a
  probe = Eq.trans (Eq.cong₂ _+_ (sform1-₀₁ a b) (sform-pIˡ ps))
                   (+-identityʳ a)

  -- Applying S twice: the two ×1 phases add to ι a, and the Z-exponent
  -- returns to b because a + a = 0.
  lhs : cact (S • S) (s , (a , b) ∷ ps) ≡ (s + ι a , (a , b) ∷ ps)
  lhs = Eq.cong₂ _,_
    (Eq.trans (+-assoc s (inclΦ a) (inclΦ a)) (Eq.cong (s +_) (incl-2 a)))
    (Eq.cong (λ □ → (a , □) ∷ ps)
      (Eq.trans (+-assoc b a a)
        (Eq.trans (Eq.cong (b +_) (x+x a)) (+-identityʳ b))))

  rhs : cact (incl (pZ ∷ pIₙ)) (s , (a , b) ∷ ps) ≡ (s + ι a , (a , b) ∷ ps)
  rhs = Eq.trans (cact-pauliWord (pZ ∷ pIₙ) s ((a , b) ∷ ps))
                 (Eq.cong (λ □ → s + ι □ , (a , b) ∷ ps) probe)
