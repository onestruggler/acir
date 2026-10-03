------------------------------------------------------------------------
-- Presentations of groups
--
-- The arithmetic of Figure 1's Legendre symbol.
--
-- Figure1.Syntactics computes (a/p)_L by Euler's criterion: it tests
-- whether a^((p-1)/2) is 1, and reads "yes" as the empty word and "no"
-- as the scalar -1.  This file is what that test needs to behave like
-- a character of ℤₚ*, for the primitive root g fixed by the module
-- parameters.
--
-- In ℤ/pℤ.  For every unit a, and in particular for h = g^((p-1)/2),
--
--   * a^((p-1)/2) squares to 1 (`euler-square`, `h²`): p is odd, so
--     (p-1)/2 + (p-1)/2 = p - 1, and Fermat's little theorem applies;
--   * hence a^((p-1)/2) = ±1 (`euler-cases`, `h-cases`): ℤ/pℤ is a
--     field, so (x - 1)(x + 1) = 0 forces a factor to vanish
--     (`square-one`);
--   * and the two cases are distinct: -1 ≠ 1 (`-₁≢₁`), as p ≥ 3.
--
-- In words.  `Signs` reads Euler's test into any presentation Γ, at any
-- word m with m² ≈ ε — the scalar -1 of whichever rule set uses it.
-- Its `sign` is the mirror of `legendre`, and the two facts proved for
-- it are the ones a rule over the multipliers M_a needs:
--
--   * multiplicativity along the powers of g (`sign-g^`): the sign of
--     g^k is the k-th power of the sign of g;
--   * the sign of -1 (`sign-₋₁`): it cancels m^((p-1)/2).
--
-- Both come from one observation, `sign-pow`: when a^((p-1)/2) is
-- (-1)^j, the sign of a is m^j.  Then (g^k)^((p-1)/2) = h^k, which is 1
-- if h = 1 and (-1)^k if h = -1; and (-1)^((p-1)/2) is (-1)^j with
-- j = (p-1)/2 itself.  Only parity is ever used, never Euler's theorem
-- that the test detects squares.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Legendre
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Empty using (⊥-elim)
import Data.Fin.Properties as FP
open import Data.Nat using (⌊_/2⌋)
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Product using (proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≢_ ; module ≡-Reasoning)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary using (Dec ; yes ; no)

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-1*x≈-x ; ⁻¹-anti-homo‿- ; +-inverseˡ-unique ; x∙y⁻¹≈ε⇒x≈y)
open import Word.Base using (Word ; WRel ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP

import Examples.Groups.Clifford.Qupit.SemSHExp p-3 p-prime as SHE
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen as F

open Primitive-Root-Modp' g* g-gen using (g′ ; g^_)

------------------------------------------------------------------------
-- Halving p - 1
--
-- p = 1 + 2q, so p - 1 = q + q and its floor-half is q exactly.

half-double : F.p-1/2 Nat.+ F.p-1/2 ≡ p-1
half-double = Eq.trans (Eq.cong₂ Nat._+_ half half) (Eq.sym p-1≡q+q)
  where
  q = proj₁ SHE.p-odd

  p-1≡q+q : p-1 ≡ q Nat.+ q
  p-1≡q+q = Eq.trans (NP.suc-injective (proj₂ SHE.p-odd))
                     (Eq.cong (q Nat.+_) (NP.+-identityʳ q))

  half : F.p-1/2 ≡ q
  half = Eq.trans (Eq.cong ⌊_/2⌋ p-1≡q+q) (Eq.sym (NP.n≡⌊n+n/2⌋ q))

------------------------------------------------------------------------
-- Squares of one in a field
--
-- (x - 1)(x + 1) = x² - 1, and a nonzero factor can be cancelled by
-- its inverse.  The ring solver is no help here: it cannot see that
-- -1 + 1 is 0 when p is a variable, so the expansion is by hand.

private
  cancelˡ : ∀ {u v : ℤ ₚ} → u ≢ ₀ → u * v ≡ ₀ → v ≡ ₀
  cancelˡ {u} {v} u≢0 uv≡0 = begin
    v              ≡⟨ Eq.sym (*-identityˡ v) ⟩
    ₁ * v          ≡⟨ Eq.cong (_* v) (Eq.sym (lemma-⁻¹ˡ u {{nz}})) ⟩
    u⁻¹ * u * v    ≡⟨ *-assoc u⁻¹ u v ⟩
    u⁻¹ * (u * v)  ≡⟨ Eq.cong (u⁻¹ *_) uv≡0 ⟩
    u⁻¹ * ₀        ≡⟨ *-zeroʳ u⁻¹ ⟩
    ₀              ∎
    where
    open ≡-Reasoning
    nz = nztoℕ {y = u} {neq0 = u≢0}
    u⁻¹ = _⁻¹' u {{nz}}

  difference-of-squares : ∀ (x : ℤ ₚ) → x * x ≡ ₁ →
    (x + - ₁) * (x + ₁) ≡ ₀
  difference-of-squares x x²≡1 = begin
    u * (x + ₁)            ≡⟨ *-distribˡ-+ u x ₁ ⟩
    u * x + u * ₁          ≡⟨ Eq.cong₂ _+_ (*-distribʳ-+ x x (- ₁))
                                           (*-identityʳ u) ⟩
    (x * x + - ₁ * x) + u  ≡⟨ Eq.cong (λ z → (z + - ₁ * x) + u) x²≡1 ⟩
    (₁ + - ₁ * x) + u      ≡⟨ Eq.cong (λ z → (₁ + z) + u) (-1*x≈-x x) ⟩
    (₁ + - x) + u          ≡⟨ Eq.cong (_+ u)
                                (Eq.sym (⁻¹-anti-homo‿- x ₁)) ⟩
    - u + u                ≡⟨ +-inverseˡ u ⟩
    ₀                      ∎
    where
    open ≡-Reasoning
    u = x + - ₁

square-one : ∀ (x : ℤ ₚ) → x * x ≡ ₁ → (x ≡ ₁) ⊎ (x ≡ - ₁)
square-one x x²≡1 with x FP.≡? ₁
... | yes x≡1 = inj₁ x≡1
... | no  x≢1 =
  inj₂ (+-inverseˡ-unique x ₁
         (cancelˡ (λ e → x≢1 (x∙y⁻¹≈ε⇒x≈y x ₁ e))
                  (difference-of-squares x x²≡1)))

------------------------------------------------------------------------
-- Euler's test squares to one
--
-- a^((p-1)/2) · a^((p-1)/2) = a^(p-1) = 1, for every unit a.

euler-square : ∀ ((a , _) : ℤ* ₚ) →
  a ^′ F.p-1/2 * a ^′ F.p-1/2 ≡ ₁
euler-square a*@(a , _) = begin
  a ^′ F.p-1/2 * a ^′ F.p-1/2   ≡⟨ +-^′-distribʳ a F.p-1/2 F.p-1/2 ⟩
  a ^′ (F.p-1/2 Nat.+ F.p-1/2)  ≡⟨ Eq.cong (a ^′_) half-double ⟩
  a ^′ p-1                      ≡⟨ Fermat's-little-theorem a* ⟩
  ₁                             ∎
  where open ≡-Reasoning

euler-cases : ∀ ((a , _) : ℤ* ₚ) →
  (a ^′ F.p-1/2 ≡ ₁) ⊎ (a ^′ F.p-1/2 ≡ - ₁)
euler-cases a*@(a , _) = square-one (a ^′ F.p-1/2) (euler-square a*)

------------------------------------------------------------------------
-- The primitive root's test

h : ℤ ₚ
h = g ^′ F.p-1/2

h² : h * h ≡ ₁
h² = euler-square g*

h-cases : (h ≡ ₁) ⊎ (h ≡ - ₁)
h-cases = euler-cases g*

------------------------------------------------------------------------
-- -1 is not 1
--
-- Its representative is p - 1, which is at least 2.

-₁≢₁ : _≢_ {A = ℤ ₚ} (- ₁) ₁
-₁≢₁ e with Eq.trans (Eq.sym lemma-toℕ-1ₚ) (Eq.cong toℕ e)
... | ()

private
  toℕ-₋₁≢1 : ∀ {y : ℤ ₚ} → y ≡ - ₁ → toℕ y ≢ 1
  toℕ-₋₁≢1 Eq.refl e = -₁≢₁ (FP.toℕ-injective e)

------------------------------------------------------------------------
-- Powers of -1
--
-- (-1)^(2q) = 1 and (-1)^(1+2q) = -1.

neg-pow-even : ∀ q → _≡_ {A = ℤ ₚ} ((- ₁) ^′ (2 Nat.* q)) ₁
neg-pow-even q = begin
  (- ₁) ^′ (2 Nat.* q)  ≡⟨ lemma-^^-* (- ₁) 2 q ⟩
  ((- ₁) ^′ 2) ^′ q     ≡⟨ Eq.cong (_^′ q) sq ⟩
  ₁ ^′ q                ≡⟨ 1^k=1 q ⟩
  ₁                     ∎
  where
  open ≡-Reasoning
  sq : _≡_ {A = ℤ ₚ} ((- ₁) ^′ 2) ₁
  sq = Eq.trans (Eq.cong (- ₁ *_) (*-identityʳ (- ₁))) aux-₁²

neg-pow-odd : ∀ q →
  _≡_ {A = ℤ ₚ} ((- ₁) ^′ (1 Nat.+ 2 Nat.* q)) (- ₁)
neg-pow-odd q =
  Eq.trans (Eq.cong (- ₁ *_) (neg-pow-even q)) (*-identityʳ (- ₁))

------------------------------------------------------------------------
-- The sign, in any presentation with an involution
--
-- `sign-by` is `F.legendre-by` with -1ˢ replaced by m.

module Signs {A : Set} (Γ : WRel A) (m : Word A)
  (m²≈ε : PB._≈_ Γ (m • m) ε) where

  open PB Γ using (_≈_ ; refl ; sym ; trans ; cong ; refl' ; right-unit)
  open PP Γ using (^^ ; ^-cong ; ^-suc ; ^-+ ; ε^k=ε)

  sign-by : ∀ {y : ℤ ₚ} → Dec (toℕ y ≡ 1) → Word A
  sign-by (yes _) = ε
  sign-by (no _)  = m

  sign : ℤ* ₚ → Word A
  sign x = sign-by (F.is-one (toℕ (x .proj₁ ^′ F.p-1/2)))

  ----------------------------------------------------------------------
  -- Reading the test off its value

  sign-by-one : ∀ {y : ℤ ₚ} (d : Dec (toℕ y ≡ 1)) → y ≡ ₁ →
    sign-by d ≡ ε
  sign-by-one (yes _) _  = Eq.refl
  sign-by-one (no ¬e) e = ⊥-elim (¬e (Eq.cong toℕ e))

  sign-by-neg : ∀ {y : ℤ ₚ} (d : Dec (toℕ y ≡ 1)) → y ≡ - ₁ →
    sign-by d ≡ m
  sign-by-neg (yes t) e = ⊥-elim (toℕ-₋₁≢1 e t)
  sign-by-neg (no _)  _ = Eq.refl

  ----------------------------------------------------------------------
  -- Powers of m depend only on parity

  m^even : ∀ q → m ^ (2 Nat.* q) ≈ ε
  m^even q =
    trans (sym (^^ m 2 q)) (trans (^-cong (m • m) ε q m²≈ε) (ε^k=ε q))

  m^odd : ∀ q → m ^ (1 Nat.+ 2 Nat.* q) ≈ m
  m^odd q = trans (^-suc m (2 Nat.* q))
                  (trans (cong refl (m^even q)) right-unit)

  m^j•m^j : ∀ j → m ^ j • m ^ j ≈ ε
  m^j•m^j j = trans (sym (^-+ m j j))
                    (trans (refl' (Eq.cong (m ^_) j+j≡2j)) (m^even j))
    where
    j+j≡2j : j Nat.+ j ≡ 2 Nat.* j
    j+j≡2j = Eq.cong (j Nat.+_) (Eq.sym (NP.+-identityʳ j))

  ----------------------------------------------------------------------
  -- The sign of a power of -1

  sign-pow : ∀ j {y : ℤ ₚ} (d : Dec (toℕ y ≡ 1)) → y ≡ (- ₁) ^′ j →
    sign-by d ≈ m ^ j
  sign-pow j d e with SHE.parity j
  ... | inj₁ (q , j≡2q) =
    trans (refl' (sign-by-one d (Eq.trans e (Eq.trans
            (Eq.cong ((- ₁) ^′_) j≡2q) (neg-pow-even q)))))
          (sym (trans (refl' (Eq.cong (m ^_) j≡2q)) (m^even q)))
  ... | inj₂ (q , j≡1+2q) =
    trans (refl' (sign-by-neg d (Eq.trans e (Eq.trans
            (Eq.cong ((- ₁) ^′_) j≡1+2q) (neg-pow-odd q)))))
          (sym (trans (refl' (Eq.cong (m ^_) j≡1+2q)) (m^odd q)))

  ----------------------------------------------------------------------
  -- Multiplicativity along the powers of g
  --
  -- (g^k)^((p-1)/2) = h^k, which is 1 or (-1)^k as h is 1 or -1.  The
  -- case on h is an argument rather than a `with`: abstracting over
  -- `h-cases` makes Agda normalise the goal, and the normal form of
  -- `sign (g^ k)` — modular arithmetic at a symbolic p — does not fit
  -- in memory.

  private
    sign-g^-by : ∀ (k : ℤ ₚ) → (h ≡ ₁) ⊎ (h ≡ - ₁) →
      sign (g^ k) ≈ sign g′ ^ toℕ k
    sign-g^-by k (inj₁ h≡1) =
      trans (refl' (sign-by-one {y = y} (F.is-one (toℕ y))
              (Eq.trans swap (Eq.trans (Eq.cong (_^′ toℕ k) h≡1)
                                       (1^k=1 (toℕ k))))))
            (sym (trans (refl' (Eq.cong (_^ toℕ k) sign-g≡ε))
                        (ε^k=ε (toℕ k))))
      where
      y = g ^′ toℕ k ^′ F.p-1/2
      swap : y ≡ h ^′ toℕ k
      swap = lemma-^^-comm g F.p-1/2 (toℕ k)
      sign-g≡ε : sign g′ ≡ ε
      sign-g≡ε = sign-by-one {y = h} (F.is-one (toℕ h)) h≡1
    sign-g^-by k (inj₂ h≡-1) =
      trans (sign-pow (toℕ k) {y = y} (F.is-one (toℕ y))
              (Eq.trans swap (Eq.cong (_^′ toℕ k) h≡-1)))
            (sym (refl' (Eq.cong (_^ toℕ k) sign-g≡m)))
      where
      y = g ^′ toℕ k ^′ F.p-1/2
      swap : y ≡ h ^′ toℕ k
      swap = lemma-^^-comm g F.p-1/2 (toℕ k)
      sign-g≡m : sign g′ ≡ m
      sign-g≡m = sign-by-neg {y = h} (F.is-one (toℕ h)) h≡-1

  sign-g^ : ∀ (k : ℤ ₚ) → sign (g^ k) ≈ sign g′ ^ toℕ k
  sign-g^ k = sign-g^-by k h-cases

  ----------------------------------------------------------------------
  -- The sign of -1
  --
  -- (-1)^((p-1)/2) is (-1)^j with j = (p-1)/2, so its sign is
  -- m^((p-1)/2), which cancels against itself.

  sign-₋₁ : sign -'₁ • m ^ F.p-1/2 ≈ ε
  sign-₋₁ =
    trans (cong (sign-pow F.p-1/2 {y = y} (F.is-one (toℕ y)) Eq.refl)
                refl)
          (m^j•m^j F.p-1/2)
    where
    y = -'₁ .proj₁ ^′ F.p-1/2
