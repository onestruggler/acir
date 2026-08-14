------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantic targets for the qupit Clifford development.
--
-- Three groups, for an odd prime p = 3 + p-3:
--
--   * the scalars ⟨ω⟩, written ω^ k for k : ℤ/pℤ, with ω^p = 1;
--   * the semidirect product Pauli n ⋊ Sp(2n, ℤ/pℤ), the qupit Clifford
--     group *modulo scalars* — the semantic counterpart of the
--     presentation in Simplified-V1.Syntactics (re-exported from
--     Examples.Construct.SemiDirectProduct.Clifford);
--   * the Clifford group *with* scalars: the central extension
--
--       1 ─→ ⟨ω⟩ ─→ Clifford n ─→ Pauli n ⋊ Sp(2n, ℤ/pℤ) ─→ 1
--
--     whose multiplication twists the scalar by half the symplectic
--     form,
--
--       (ω^e , P , S) · (ω^f , Q , T)
--          = (ω^(e + f + ½·sform P (ap S Q)) , P +ₚ ap S Q , S ∘ˢ T).
--
-- Halving is available because p is odd, and it is what makes the
-- cocycle symplectically invariant: sform is preserved by every
-- symplectic transformation, hence so is the ½·sform twist, and the
-- product is associative.  The payoff is `heisenberg` below — two
-- Paulis commute only up to ω^(sform P Q) — so this extension really is
-- the Clifford group, not the direct product ⟨ω⟩ × (Pauli ⋊ Sp).
--
-- The third group is built as an instance of
-- ForStdlib.Algebra.Construct.CentralExtension: the content of this file
-- is the Cocycle record `weyl` — that ½·sform is normalised and
-- satisfies the cocycle identity — and the group, its laws and its short
-- exact sequence then come from the library.  That is also what pins
-- down where the scalars sit: a central extension is exactly one whose
-- kernel is central, and `incl-central` is the library's construction
-- read back here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Primality using (Prime)

open import Notations

module Examples.Groups.Clifford.Qupit.Semantics
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Algebra.Structures using (IsGroup)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ<)
import Data.Nat as Nat
open import Data.Nat.DivMod
  using (_%_ ; m%n<n ; n%n≡0 ; %-distribˡ-+ ; m%n%n≡m%n ; m<n⇒m%n≡m)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
import ForStdlib.Algebra.Construct.CentralExtension as CE
open CE using (Cocycle)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; sform ; sform1 ; sform1-antisym ; pI ; pIₙ
        ; _+₁_ ; -₁_ ; _+ₚ_ ; -ₚ_ ; +ₚ-comm )
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; εˢ ; _∘ˢ_ ; _⁻¹ˢ)
open Symplectic
open import Examples.Construct.SemiDirectProduct.Clifford p-2 p-prime
  using (Pauli⋊Sp-group ; ap-ε) public

------------------------------------------------------------------------
-- The group of scalars ⟨ω⟩
--
-- ω^ k for k : ℤ/pℤ, multiplied by adding exponents: this is ℤ/pℤ
-- written multiplicatively.  Keeping it a type of its own (rather than
-- reusing +-0-group) is what lets the extension below read as phases
-- times Clifford data.

record Scalar : Set where
  constructor ω^_
  field
    exponent : ℤ ₚ

infixl 7 _·ω_
infix  8 _⁻¹ω

_·ω_ : Scalar → Scalar → Scalar
ω^ j ·ω ω^ k = ω^ (j + k)

1ω : Scalar
1ω = ω^ ₀

_⁻¹ω : Scalar → Scalar
(ω^ k) ⁻¹ω = ω^ (- k)

-- The primitive scalar itself.
ω : Scalar
ω = ω^ ₁

-- Each group law is the corresponding law of ℤ/pℤ under ω^_.
Scalar-isGroup : IsGroup _≡_ _·ω_ 1ω _⁻¹ω
Scalar-isGroup = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = Eq.isEquivalence
        ; ∙-cong        = Eq.cong₂ _·ω_
        }
      ; assoc = λ (ω^ i) (ω^ j) (ω^ k) → Eq.cong ω^_ (+-assoc i j k)
      }
    ; identity = (λ (ω^ k) → Eq.cong ω^_ (+-identityˡ k))
               , (λ (ω^ k) → Eq.cong ω^_ (+-identityʳ k))
    }
  ; inverse = (λ (ω^ k) → Eq.cong ω^_ (+-inverseˡ k))
            , (λ (ω^ k) → Eq.cong ω^_ (+-inverseʳ k))
  ; ⁻¹-cong = Eq.cong _⁻¹ω
  }

-- The scalars are abelian, which is what the kernel of a central
-- extension has to be.
Scalar-abelianGroup : AbelianGroup 0ℓ 0ℓ
Scalar-abelianGroup = record
  { isAbelianGroup = record
    { isGroup = Scalar-isGroup
    ; comm    = λ (ω^ i) (ω^ j) → Eq.cong ω^_ (+-comm i j)
    }
  }

Scalar-group : Group 0ℓ 0ℓ
Scalar-group = AbelianGroup.group Scalar-abelianGroup

------------------------------------------------------------------------
-- ω has order p
--
-- The k-th power of ω has as exponent the k-fold sum of ₁, which is the
-- image of k under ℕ ↠ ℤ/pℤ; at k = p that is ₀.

infixl 9 _^ω_
_^ω_ : Scalar → ℕ → Scalar
s ^ω ₀      = 1ω
s ^ω (₁₊ k) = s ·ω (s ^ω k)

-- The k-fold sum of ₁ in ℤ/pℤ.
ones : ℕ → ℤ ₚ
ones ₀      = ₀
ones (₁₊ k) = ₁ + ones k

ω-pow : ∀ k → ω ^ω k ≡ ω^ (ones k)
ω-pow ₀      = Eq.refl
ω-pow (₁₊ k) = Eq.cong (ω ·ω_) (ω-pow k)

-- Adding in ℤ/pℤ adds representatives and reduces.
toℕ-+ : ∀ (a b : ℤ ₚ) → toℕ (a + b) ≡ (toℕ a Nat.+ toℕ b) % p
toℕ-+ a b = toℕ-fromℕ< (m%n<n (toℕ a Nat.+ toℕ b) p)

-- p is a successor, so mod-helper reduces on the spot.
0%p≡0 : 0 % p ≡ 0
0%p≡0 = Eq.refl

ones-% : ∀ k → toℕ (ones k) ≡ k % p
ones-% ₀      = Eq.sym 0%p≡0
ones-% (₁₊ k) = begin
  toℕ (₁ + ones k)               ≡⟨ toℕ-+ ₁ (ones k) ⟩
  (1 Nat.+ toℕ (ones k)) % p     ≡⟨ Eq.cong (λ z → (1 Nat.+ z) % p) (ones-% k) ⟩
  (1 Nat.+ k % p) % p            ≡⟨ %-distribˡ-+ 1 (k % p) p ⟩
  (1 % p Nat.+ (k % p) % p) % p  ≡⟨ Eq.cong (λ z → (1 % p Nat.+ z) % p) (m%n%n≡m%n k p) ⟩
  (1 % p Nat.+ k % p) % p        ≡⟨ Eq.sym (%-distribˡ-+ 1 k p) ⟩
  (1 Nat.+ k) % p                ∎
  where open Eq.≡-Reasoning

ones-p : ones p ≡ ₀
ones-p = toℕ-injective (Eq.trans (ones-% p) (n%n≡0 p))

-- ω^p = 1, the defining law of the scalar group.
ω-order : ω ^ω p ≡ 1ω
ω-order = Eq.trans (ω-pow p) (Eq.cong ω^_ ones-p)

------------------------------------------------------------------------
-- One half
--
-- Available because p is odd; this is the coefficient of the cocycle.

2ₚ : ℤ ₚ
2ₚ = ₂

1/2 : ℤ ₚ
1/2 = ((2ₚ , λ ()) ⁻¹) .proj₁

private
  2<p : 2 < p
  2<p = s≤s (s≤s (s≤s z≤n))

  1+1≡2 : 1ₚ + 1ₚ ≡ 2ₚ
  1+1≡2 = toℕ-injective (Eq.trans (toℕ-+ 1ₚ 1ₚ) (m<n⇒m%n≡m 2<p))

  half*2 : 1/2 * 2ₚ ≡ 1ₚ
  half*2 = lemma-⁻¹ˡ 2ₚ {{nztoℕ {y = 2ₚ} {neq0 = λ ()}}}

half+half : 1/2 + 1/2 ≡ 1ₚ
half+half = begin
  1/2 + 1/2            ≡⟨ Eq.sym (Eq.cong₂ _+_ (*-identityʳ 1/2) (*-identityʳ 1/2)) ⟩
  1/2 * 1ₚ + 1/2 * 1ₚ  ≡⟨ Eq.sym (*-distribˡ-+ 1/2 1ₚ 1ₚ) ⟩
  1/2 * (1ₚ + 1ₚ)      ≡⟨ Eq.cong (1/2 *_) 1+1≡2 ⟩
  1/2 * 2ₚ             ≡⟨ half*2 ⟩
  1ₚ                   ∎
  where open Eq.≡-Reasoning

-- Two halves of x make x: this is what turns the ½·sform twist into the
-- full symplectic form in `heisenberg`.
half-half : ∀ (x : ℤ ₚ) → 1/2 * x + 1/2 * x ≡ x
half-half x = begin
  1/2 * x + 1/2 * x  ≡⟨ Eq.sym (*-distribʳ-+ x 1/2 1/2) ⟩
  (1/2 + 1/2) * x    ≡⟨ Eq.cong (_* x) half+half ⟩
  1ₚ * x             ≡⟨ *-identityˡ x ⟩
  x                  ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Bilinearity of the symplectic form
--
-- sform is ℤ/pℤ-bilinear, vanishes on the identity Pauli and is
-- alternating.  (These belong next to sform in
-- Examples.Groups.ProjectivePauli.Semantics; they live here while only this
-- development needs them.)

private
  -- Rearrangements in the commutative monoid (ℤ/pℤ , +).
  +-swap-middle : ∀ (a b c d : ℤ ₚ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-swap-middle a b c d = begin
    (a + b) + (c + d)  ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))  ≡⟨ Eq.cong (a +_) (Eq.sym (+-assoc b c d)) ⟩
    a + ((b + c) + d)  ≡⟨ Eq.cong (λ z → a + (z + d)) (+-comm b c) ⟩
    a + ((c + b) + d)  ≡⟨ Eq.cong (a +_) (+-assoc c b d) ⟩
    a + (c + (b + d))  ≡⟨ Eq.sym (+-assoc a c (b + d)) ⟩
    (a + c) + (b + d)  ∎
    where open Eq.≡-Reasoning

  +-swap-right : ∀ (a b c : ℤ ₚ) → (a + b) + c ≡ (a + c) + b
  +-swap-right a b c = begin
    (a + b) + c  ≡⟨ +-assoc a b c ⟩
    a + (b + c)  ≡⟨ Eq.cong (a +_) (+-comm b c) ⟩
    a + (c + b)  ≡⟨ Eq.sym (+-assoc a c b) ⟩
    (a + c) + b  ∎
    where open Eq.≡-Reasoning

  +-rotate : ∀ (x y z : ℤ ₚ) → x + (y + z) ≡ z + (x + y)
  +-rotate x y z = Eq.trans (Eq.sym (+-assoc x y z)) (+-comm (x + y) z)

sform1-+ˡ : ∀ (x y z : Pauli1) → sform1 (x +₁ y) z ≡ sform1 x z + sform1 y z
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

sform1-+ʳ : ∀ (x y z : Pauli1) → sform1 x (y +₁ z) ≡ sform1 x y + sform1 x z
sform1-+ʳ (a , b) (c , d) (c' , d') = begin
  (- a) * (d + d') + (c + c') * b
    ≡⟨ Eq.cong₂ _+_ (*-distribˡ-+ (- a) d d') (*-distribʳ-+ b c c') ⟩
  ((- a) * d + (- a) * d') + (c * b + c' * b)
    ≡⟨ +-swap-middle ((- a) * d) ((- a) * d') (c * b) (c' * b) ⟩
  ((- a) * d + c * b) + ((- a) * d' + c' * b) ∎
  where open Eq.≡-Reasoning

sform-+ˡ : ∀ {n} (P Q R : Pauli n) → sform (P +ₚ Q) R ≡ sform P R + sform Q R
sform-+ˡ []       []       []       = Eq.sym (+-identityʳ ₀)
sform-+ˡ (x ∷ xs) (y ∷ ys) (z ∷ zs) = begin
  sform1 (x +₁ y) z + sform (xs +ₚ ys) zs
    ≡⟨ Eq.cong₂ _+_ (sform1-+ˡ x y z) (sform-+ˡ xs ys zs) ⟩
  (sform1 x z + sform1 y z) + (sform xs zs + sform ys zs)
    ≡⟨ +-swap-middle (sform1 x z) (sform1 y z) (sform xs zs) (sform ys zs) ⟩
  (sform1 x z + sform xs zs) + (sform1 y z + sform ys zs) ∎
  where open Eq.≡-Reasoning

sform-+ʳ : ∀ {n} (P Q R : Pauli n) → sform P (Q +ₚ R) ≡ sform P Q + sform P R
sform-+ʳ []       []       []       = Eq.sym (+-identityʳ ₀)
sform-+ʳ (x ∷ xs) (y ∷ ys) (z ∷ zs) = begin
  sform1 x (y +₁ z) + sform xs (ys +ₚ zs)
    ≡⟨ Eq.cong₂ _+_ (sform1-+ʳ x y z) (sform-+ʳ xs ys zs) ⟩
  (sform1 x y + sform1 x z) + (sform xs ys + sform xs zs)
    ≡⟨ +-swap-middle (sform1 x y) (sform1 x z) (sform xs ys) (sform xs zs) ⟩
  (sform1 x y + sform xs ys) + (sform1 x z + sform xs zs) ∎
  where open Eq.≡-Reasoning

-- sform vanishes on the identity Pauli, on either side.
sform1-pIʳ : ∀ (x : Pauli1) → sform1 x pI ≡ ₀
sform1-pIʳ (a , b) =
  Eq.trans (Eq.cong₂ _+_ (*-zeroʳ (- a)) (*-zeroˡ b)) (+-identityˡ ₀)

sform1-pIˡ : ∀ (x : Pauli1) → sform1 pI x ≡ ₀
sform1-pIˡ (c , d) =
  Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (_* d) -0#≈0#) (*-zeroˡ d))
                         (*-zeroʳ c))
           (+-identityˡ ₀)

sform-pIʳ : ∀ {n} (P : Pauli n) → sform P pIₙ ≡ ₀
sform-pIʳ []       = Eq.refl
sform-pIʳ (x ∷ xs) =
  Eq.trans (Eq.cong₂ _+_ (sform1-pIʳ x) (sform-pIʳ xs)) (+-identityʳ ₀)

sform-pIˡ : ∀ {n} (P : Pauli n) → sform pIₙ P ≡ ₀
sform-pIˡ []       = Eq.refl
sform-pIˡ (x ∷ xs) =
  Eq.trans (Eq.cong₂ _+_ (sform1-pIˡ x) (sform-pIˡ xs)) (+-identityʳ ₀)

-- sform is antisymmetric, hence alternating on P and -ₚ P.
sform-antisym : ∀ {n} (P Q : Pauli n) → sform P Q ≡ - sform Q P
sform-antisym []       []       = Eq.sym -0#≈0#
sform-antisym (x ∷ xs) (y ∷ ys) = begin
  sform1 x y + sform xs ys
    ≡⟨ Eq.cong₂ _+_ (sform1-antisym x y) (sform-antisym xs ys) ⟩
  (- sform1 y x) + (- sform ys xs)
    ≡⟨ -‿+-comm (sform1 y x) (sform ys xs) ⟩
  - (sform1 y x + sform ys xs) ∎
  where open Eq.≡-Reasoning

sform1-negʳ : ∀ (x : Pauli1) → sform1 x (-₁ x) ≡ ₀
sform1-negʳ (a , b) = begin
  (- a) * (- b) + (- a) * b
    ≡⟨ Eq.cong₂ _+_ neg-neg (Eq.sym (-‿distribˡ-* a b)) ⟩
  a * b + (- (a * b))
    ≡⟨ +-inverseʳ (a * b) ⟩
  ₀ ∎
  where
  open Eq.≡-Reasoning
  neg-neg : (- a) * (- b) ≡ a * b
  neg-neg = begin
    (- a) * (- b)  ≡⟨ Eq.sym (-‿distribˡ-* a (- b)) ⟩
    - (a * (- b))  ≡⟨ Eq.cong -_ (Eq.sym (-‿distribʳ-* a b)) ⟩
    - (- (a * b))  ≡⟨ -‿involutive (a * b) ⟩
    a * b          ∎

sform-negʳ : ∀ {n} (P : Pauli n) → sform P (-ₚ P) ≡ ₀
sform-negʳ []       = Eq.refl
sform-negʳ (x ∷ xs) =
  Eq.trans (Eq.cong₂ _+_ (sform1-negʳ x) (sform-negʳ xs)) (+-identityʳ ₀)

sform-negˡ : ∀ {n} (P : Pauli n) → sform (-ₚ P) P ≡ ₀
sform-negˡ P =
  Eq.trans (sform-antisym (-ₚ P) P) (Eq.trans (Eq.cong -_ (sform-negʳ P)) -0#≈0#)

------------------------------------------------------------------------
-- The Clifford group with scalars
--
-- The central extension of Pauli n ⋊ Sp(2n, ℤ/pℤ) by ⟨ω⟩, with the Weyl
-- cocycle ½·sform.  The second component and its laws are inherited
-- wholesale from the semidirect product; all the work is in the scalar.

module _ (n : ℕ) where

  private
    module H = Group (Pauli⋊Sp-group n)

  ----------------------------------------------------------------------
  -- The cocycle

  -- The phase picked up when multiplying: half the symplectic form of
  -- the left Pauli against the transported right one.
  cocy : H.Carrier → H.Carrier → ℤ ₚ
  cocy (P , S) (Q , _) = 1/2 * sform P (ap S Q)

  cocy-cong : ∀ {g g' h h'} → g H.≈ g' → h H.≈ h' → cocy g h ≡ cocy g' h'
  cocy-cong {P , S} {_ , S'} {Q , _} {_ , _} (Eq.refl , S≈S') (Eq.refl , _) =
    Eq.cong (λ z → 1/2 * sform P z) (S≈S' Q)

  -- Normalisation: the cocycle vanishes whenever an argument is trivial.
  cocy-εˡ : ∀ g → cocy H.ε g ≡ ₀
  cocy-εˡ (Q , _) =
    Eq.trans (Eq.cong (1/2 *_) (sform-pIˡ Q)) (*-zeroʳ 1/2)

  cocy-εʳ : ∀ g → cocy g H.ε ≡ ₀
  cocy-εʳ (P , S) = begin
    1/2 * sform P (ap S pIₙ)  ≡⟨ Eq.cong (λ z → 1/2 * sform P z) (ap-ε S) ⟩
    1/2 * sform P pIₙ         ≡⟨ Eq.cong (1/2 *_) (sform-pIʳ P) ⟩
    1/2 * ₀                   ≡⟨ *-zeroʳ 1/2 ⟩
    ₀                         ∎
    where open Eq.≡-Reasoning

  -- …and on an element against its inverse, on either side.  (The
  -- inverse in the semidirect product is (ap⁻¹ S (-ₚ P) , S ⁻¹ˢ).)
  cocy-invʳ : ∀ g → cocy g (g H.⁻¹) ≡ ₀
  cocy-invʳ (P , S) = begin
    1/2 * sform P (ap S (ap⁻¹ S (-ₚ P)))
      ≡⟨ Eq.cong (λ z → 1/2 * sform P z) (invʳ S (-ₚ P)) ⟩
    1/2 * sform P (-ₚ P)  ≡⟨ Eq.cong (1/2 *_) (sform-negʳ P) ⟩
    1/2 * ₀               ≡⟨ *-zeroʳ 1/2 ⟩
    ₀                     ∎
    where open Eq.≡-Reasoning

  -- The cocycle identity.  This is where symplectic invariance of sform
  -- is used, and it is exactly what makes the product below associative.
  cocy-assoc : ∀ g h k →
               cocy g h + cocy (g H.∙ h) k ≡ cocy h k + cocy g (h H.∙ k)
  cocy-assoc (P₁ , S₁) (P₂ , S₂) (P₃ , S₃) = begin
    x + 1/2 * sform (P₁ +ₚ ap S₁ P₂) (ap S₁ (ap S₂ P₃))
      ≡⟨ Eq.cong (λ z → x + 1/2 * z) (sform-+ˡ P₁ (ap S₁ P₂) (ap S₁ (ap S₂ P₃))) ⟩
    x + 1/2 * (sform P₁ (ap S₁ (ap S₂ P₃)) + sform (ap S₁ P₂) (ap S₁ (ap S₂ P₃)))
      ≡⟨ Eq.cong (λ z → x + 1/2 * (sform P₁ (ap S₁ (ap S₂ P₃)) + z))
                 (preserves S₁ P₂ (ap S₂ P₃)) ⟩
    x + 1/2 * (sform P₁ (ap S₁ (ap S₂ P₃)) + sform P₂ (ap S₂ P₃))
      ≡⟨ Eq.cong (x +_) (*-distribˡ-+ 1/2 (sform P₁ (ap S₁ (ap S₂ P₃)))
                                          (sform P₂ (ap S₂ P₃))) ⟩
    x + (y + z)
      ≡⟨ +-rotate x y z ⟩
    z + (x + y)
      ≡⟨ Eq.cong (z +_) (Eq.sym (*-distribˡ-+ 1/2 (sform P₁ (ap S₁ P₂))
                                                  (sform P₁ (ap S₁ (ap S₂ P₃))))) ⟩
    z + 1/2 * (sform P₁ (ap S₁ P₂) + sform P₁ (ap S₁ (ap S₂ P₃)))
      ≡⟨ Eq.cong (λ w → z + 1/2 * w)
                 (Eq.sym (sform-+ʳ P₁ (ap S₁ P₂) (ap S₁ (ap S₂ P₃)))) ⟩
    z + 1/2 * sform P₁ (ap S₁ P₂ +ₚ ap S₁ (ap S₂ P₃))
      ≡⟨ Eq.cong (λ w → z + 1/2 * sform P₁ w)
                 (Eq.sym (linear-+ S₁ P₂ (ap S₂ P₃))) ⟩
    z + 1/2 * sform P₁ (ap S₁ (P₂ +ₚ ap S₂ P₃)) ∎
    where
    open Eq.≡-Reasoning
    x = 1/2 * sform P₁ (ap S₁ P₂)
    y = 1/2 * sform P₁ (ap S₁ (ap S₂ P₃))
    z = 1/2 * sform P₂ (ap S₂ P₃)

  ----------------------------------------------------------------------
  -- The Weyl cocycle
  --
  -- The three laws above, packaged for
  -- ForStdlib.Algebra.Construct.CentralExtension.  This record is the
  -- whole content of the extension; everything below it is library.

  weyl : Cocycle Scalar-abelianGroup (Pauli⋊Sp-group n)
  weyl = record
    { c       = λ g h → ω^ (cocy g h)
    ; c-cong  = λ {g} {g'} {h} {h'} eg eh →
                  Eq.cong ω^_ (cocy-cong {g} {g'} {h} {h'} eg eh)
    ; c-εˡ    = λ g → Eq.cong ω^_ (cocy-εˡ g)
    ; c-εʳ    = λ g → Eq.cong ω^_ (cocy-εʳ g)
    ; cocycle = λ g h k → Eq.cong ω^_ (cocy-assoc g h k)
    }

  ----------------------------------------------------------------------
  -- The group and the extension
  --
  -- Both are the library's, at the cocycle above.  The multiplication is
  --
  --   (ω^e , g) ·ᶜ (ω^f , h) = (ω^(e + f + cocy g h) , g ∙ h),
  --
  -- the twisted product ⟨ω⟩ ×_c (Pauli n ⋊ Sp(2n, ℤ/pℤ)), and the short
  -- exact sequence is its centralExtension — so the associativity,
  -- identity and inverse laws that used to be discharged here by hand
  -- are now the library's, and the cocycle identity is what buys them.

  Clifford-group : Group 0ℓ 0ℓ
  Clifford-group = CE.group Scalar-abelianGroup (Pauli⋊Sp-group n) weyl

  open Group Clifford-group public using ()
    renaming ( Carrier to Clifford ; _≈_ to _≈ᶜ_ ; _∙_ to _·ᶜ_
             ; ε to εᶜ ; _⁻¹ to _⁻¹ᶜ ; isGroup to Clifford-isGroup )

  Clifford-extension : Extension Scalar-group (Pauli⋊Sp-group n)
  Clifford-extension =
    CE.centralExtension Scalar-abelianGroup (Pauli⋊Sp-group n) weyl

  -- The inclusion of the scalars, as the extension supplies it.
  incl : Scalar → Clifford
  incl s = s , H.ε

  -- The library's inverse has to undo the cocycle defect as well as the
  -- scalar.  Here that defect vanishes, by cocy-invʳ, so the inverse is
  -- just the negated exponent — the formula this file used to take as
  -- the definition.
  ⁻¹ᶜ-exponent : ∀ (e : ℤ ₚ) (g : H.Carrier) →
                 ((ω^ e , g) ⁻¹ᶜ) ≈ᶜ (ω^ (- e) , g H.⁻¹)
  ⁻¹ᶜ-exponent e g =
      Eq.cong (λ z → ω^ (- z))
              (Eq.trans (Eq.cong (e +_) (cocy-invʳ g)) (+-identityʳ e))
    , H.refl {x = g H.⁻¹}

  ----------------------------------------------------------------------
  -- The extension is central, and non-trivially so

  -- The scalars commute with everything.
  incl-central : ∀ s g → (incl s ·ᶜ g) ≈ᶜ (g ·ᶜ incl s)
  incl-central (ω^ i) (ω^ e , g) =
      Eq.cong ω^_ (begin
        i + e + cocy H.ε g  ≡⟨ Eq.cong (i + e +_) (cocy-εˡ g) ⟩
        i + e + ₀           ≡⟨ Eq.cong (_+ ₀) (+-comm i e) ⟩
        e + i + ₀           ≡⟨ Eq.cong (e + i +_) (Eq.sym (cocy-εʳ g)) ⟩
        e + i + cocy g H.ε  ∎)
    , H.trans {i = H.ε H.∙ g} {j = g} {k = g H.∙ H.ε}
              (H.identityˡ g)
              (H.sym {x = g H.∙ H.ε} {y = g} (H.identityʳ g))
    where open Eq.≡-Reasoning

  -- A Pauli, lifted with trivial phase and trivial symplectic part.
  pauli : Pauli n → Clifford
  pauli P = 1ω , (P , εˢ)

  -- The Heisenberg law: two lifted Paulis commute exactly up to the
  -- scalar ω^(sform P Q).  This is what distinguishes this extension
  -- from the direct product ⟨ω⟩ × (Pauli ⋊ Sp), and it is where the two
  -- halves of the cocycle add up to a whole symplectic form.
  heisenberg : ∀ (P Q : Pauli n) →
               (pauli P ·ᶜ pauli Q)
                 ≈ᶜ (incl (ω^ (sform P Q)) ·ᶜ (pauli Q ·ᶜ pauli P))
  heisenberg P Q = Eq.cong ω^_ scalar-eq , H-eq
    where
    open Eq.≡-Reasoning
    s = sform P Q
    -- s = ½s + ½s, so s - ½s = ½s.
    half-cancel : s + (- (1/2 * s)) ≡ 1/2 * s
    half-cancel = begin
      s + (- (1/2 * s))
        ≡⟨ Eq.cong (_+ (- (1/2 * s))) (Eq.sym (half-half s)) ⟩
      (1/2 * s + 1/2 * s) + (- (1/2 * s))
        ≡⟨ +-assoc (1/2 * s) (1/2 * s) (- (1/2 * s)) ⟩
      1/2 * s + (1/2 * s + (- (1/2 * s)))
        ≡⟨ Eq.cong (1/2 * s +_) (+-inverseʳ (1/2 * s)) ⟩
      1/2 * s + ₀
        ≡⟨ +-identityʳ (1/2 * s) ⟩
      1/2 * s ∎
    -- Both sides' scalars, reduced: ½·sform P Q on the left, and
    -- sform P Q + ½·sform Q P (plus vanishing cocycles) on the right.
    scalar-eq : ₀ + ₀ + 1/2 * sform P Q
                  ≡ s + (₀ + ₀ + 1/2 * sform Q P) + cocy H.ε (Q +ₚ P , εˢ ∘ˢ εˢ)
    scalar-eq = begin
      ₀ + ₀ + 1/2 * s
        ≡⟨ Eq.cong (_+ 1/2 * s) (+-identityʳ ₀) ⟩
      ₀ + 1/2 * s
        ≡⟨ +-identityˡ (1/2 * s) ⟩
      1/2 * s
        ≡⟨ Eq.sym half-cancel ⟩
      s + (- (1/2 * s))
        ≡⟨ Eq.cong (s +_) (Eq.trans (-‿distribʳ-* 1/2 s)
                                    (Eq.sym (Eq.cong (1/2 *_) (sform-antisym Q P)))) ⟩
      s + 1/2 * sform Q P
        ≡⟨ Eq.cong (λ z → s + z) (Eq.sym (Eq.trans (Eq.cong (_+ 1/2 * sform Q P)
                                                            (+-identityʳ ₀))
                                                   (+-identityˡ (1/2 * sform Q P)))) ⟩
      s + (₀ + ₀ + 1/2 * sform Q P)
        ≡⟨ Eq.sym (+-identityʳ (s + (₀ + ₀ + 1/2 * sform Q P))) ⟩
      s + (₀ + ₀ + 1/2 * sform Q P) + ₀
        ≡⟨ Eq.cong (s + (₀ + ₀ + 1/2 * sform Q P) +_)
                   (Eq.sym (cocy-εˡ (Q +ₚ P , εˢ ∘ˢ εˢ))) ⟩
      s + (₀ + ₀ + 1/2 * sform Q P) + cocy H.ε (Q +ₚ P , εˢ ∘ˢ εˢ) ∎
    H-eq : H._≈_ (P +ₚ Q , εˢ ∘ˢ εˢ) (H.ε H.∙ (Q +ₚ P , εˢ ∘ˢ εˢ))
    H-eq = H.trans {i = P +ₚ Q , εˢ ∘ˢ εˢ}
                   {j = Q +ₚ P , εˢ ∘ˢ εˢ}
                   {k = H.ε H.∙ (Q +ₚ P , εˢ ∘ˢ εˢ)}
                   (+ₚ-comm P Q , λ _ → Eq.refl)
                   (H.sym {x = H.ε H.∙ (Q +ₚ P , εˢ ∘ˢ εˢ)}
                          {y = Q +ₚ P , εˢ ∘ˢ εˢ}
                          (H.identityˡ (Q +ₚ P , εˢ ∘ˢ εˢ)))
