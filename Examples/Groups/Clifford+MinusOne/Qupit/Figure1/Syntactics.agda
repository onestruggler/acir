------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1 of Bian, Li, Ross, van de Wetering and Zhao, "A Complete
-- and Natural Rule Set for Multi-Qudit Clifford Circuits in All Odd
-- Prime Dimensions" (arXiv:2609.40106): the sixteen rules C0–C15 for
-- n-qudit Clifford circuits over the generators
--
--     -ω,  H,  S,  CZ          (ω = e^(2πi/p), p an odd prime),
--
-- together with the derived generators of its Figure 2 / Figure 4
-- (T1–T7) that the rules are written over.
--
-- Generators.  The scalar -ω is a 0-ary gate, ν, exactly as Selinger's
-- ω is in Clifford.Qubit.Selinger.Figure8: a gate on no wires exists at
-- every width, and Circuit.Base's Lift-Relation already makes it
-- wire-independent (ω↑=ω, a structural rule) and central (comm₀, a
-- theorem of the structural rules once scalars commute with one
-- another, which with ν the only one is refl).  The paper treats -ω as
-- a global phase, so both facts are implicit there; here no axiom of
-- this module restates them.
--
-- The other scalars are powers of ν (the caption of Figure 1):
--
--     -1 = ν ^ p,      ω = ν ^ (p + 1),      λ_p² = (-1) ^ ((p-1)/2).
--
-- Reading order.  A word is read as the matrix product it denotes,
-- rightmost letter first — the convention of the whole qupit library
-- (Paper-V0 writes X = H • S • H • H • S⁻¹ • H for the paper's
-- H, S⁻¹, H², S, H drawn left to right).  So every circuit drawn in the
-- paper appears here reversed, which is also how the paper states each
-- rule as an operator equation in its soundness lemmas (A.25–A.27):
--
--     C4   M_g S = Z^((1-g)/(2g²)) S^(g⁻²) M_g
--     C9   CZ (M_g ⊗ I) = (M_g ⊗ I) CZ^g
--     C12  (S⁻¹ ⊗ S⁻¹) CX⁻¹ (I ⊗ S) CX = CZ
--     C15  (I ⊗ CZ)(CX ⊗ I) = CIZ (CX ⊗ I)(I ⊗ CZ),
--
-- with the first tensor factor the top wire, which is the shifted one
-- here (`_↑`).
--
-- Exponents (Remark 2.2 of the paper).  An exponent of ω, or of a gate
-- of order p, is an element of ℤ/pℤ; a fraction or an inverse in an
-- exponent is computed there.  So S^(a⁻¹) is S ^ toℕ (a⁻¹), and
-- (1-a)/(2a) is (1 - a) · ½ · a⁻¹.
--
-- The Legendre symbol.  T1 multiplies M_a by (a/p)_L, which is 1 if a
-- is a square mod p and -1 otherwise.  It is computed here by Euler's
-- criterion: (a/p)_L ≡ a^((p-1)/2) mod p, which is 1 or -1 by Fermat.
-- That the two agree is Euler's classical theorem and is not
-- formalised; nothing below depends on it, since every rule that
-- mentions the symbol is checked against Euler's form directly.
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

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Nat using (⌊_/2⌋)
import Data.Nat as Nat
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties

open Primitive-Root-Modp' g* g-gen using (g′ ; g^_)

------------------------------------------------------------------------
-- The gate set

data Fig1Gate : ℕ → Set where
  ν-gate  : Fig1Gate 0     -- the scalar -ω
  H-gate  : Fig1Gate 1
  S-gate  : Fig1Gate 1
  CZ-gate : Fig1Gate 2

open import Circuit.Base Fig1Gate
  using ( Gen ; Circuit ; CRel ; gate₀ ; gate₁ ; gate₂
        ; _↥ ; _↑ ; _↓ ; module Lift-Relation) public

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The generators, as one-letter words

-- The scalar generator -ω.
ν : Word (Gen n)
ν = [ gate₀ ν-gate ]ʷ

H : Word (Gen (₁₊ n))
H = [ gate₁ H-gate ]ʷ

S : Word (Gen (₁₊ n))
S = [ gate₁ S-gate ]ʷ

CZ : Word (Gen (₂₊ n))
CZ = [ gate₂ CZ-gate ]ʷ

------------------------------------------------------------------------
-- Exponents in ℤ/pℤ

1/2 : ℤ ₚ
1/2 = ((₂ , λ ()) ⁻¹) .proj₁

-- 1/8, for the exponent of T1's phase.
1/8 : ℤ ₚ
1/8 = 1/2 * 1/2 * 1/2

-- (p - 1)/2, the exponent of λ_p² and of Euler's criterion.  p is odd,
-- so the floor is exact.
p-1/2 : ℕ
p-1/2 = ⌊ p-1 /2⌋

------------------------------------------------------------------------
-- The scalars

-- -1 = (-ω)^p.
-1ˢ : Word (Gen n)
-1ˢ = ν ^ p

-- ω = (-ω)^(p+1).
ωˢ : Word (Gen n)
ωˢ = ν ^ ₁₊ p

-- ω to a power in ℤ/pℤ.
ω^ : ℤ ₚ → Word (Gen n)
ω^ t = ωˢ ^ toℕ t

-- λ_p² = e^((p-1)πi/2) = (-1)^((p-1)/2), the phase of T4.
λ² : Word (Gen n)
λ² = -1ˢ ^ p-1/2

-- The Legendre symbol (a/p)_L, by Euler's criterion: a^((p-1)/2) is
-- 1 exactly when a is a square.  The test is made on the
-- representative, toℕ y ≡ 1 being y ≡ ₁ by toℕ-injective, and is
-- spelled out rather than taken from the library, whose name for it
-- has moved between releases.
is-one : (m : ℕ) → Dec (m ≡ 1)
is-one ₀      = no (λ ())
is-one (₁₊ ₀) = yes Eq.refl
is-one (₂₊ m) = no (λ ())

legendre-by : ∀ {y : ℤ ₚ} → Dec (toℕ y ≡ 1) → Word (Gen n)
legendre-by (yes _) = ε
legendre-by (no _)  = -1ˢ

legendre : ℤ* ₚ → Word (Gen n)
legendre a* = legendre-by (is-one (toℕ (a* .proj₁ ^′ p-1/2)))

------------------------------------------------------------------------
-- Powers

S^ : ℤ ₚ → Word (Gen (₁₊ n))
S^ k = S ^ toℕ k

S⁻¹ : Word (Gen (₁₊ n))
S⁻¹ = S ^ p-1

CZ^ : ℤ ₚ → Word (Gen (₂₊ n))
CZ^ k = CZ ^ toℕ k

------------------------------------------------------------------------
-- The derived generators (Figure 4)

-- T2, T3: the Paulis.
X : Word (Gen (₁₊ n))
X = H • S • H • H • S⁻¹ • H

Z : Word (Gen (₁₊ n))
Z = H • H • S • H • H • S⁻¹

X^ : ℤ ₚ → Word (Gen (₁₊ n))
X^ k = X ^ toℕ k

Z^ : ℤ ₚ → Word (Gen (₁₊ n))
Z^ k = Z ^ toℕ k

-- T1: the multiplier by a ∈ ℤₚ*,
--
--     M_a = Z^((1-a)/(2a)) X^((1-a)/2) S^(a⁻¹) H S^a H S^(a⁻¹) H
--           · (a/p)_L · ω^((-a² + 4a - 2)/(8a)),
--
-- which maps |x⟩ to |ax⟩ on the nose (Lemma 2.15).
--
-- Its exponents, named: the Z-exponent (1-a)/(2a) and the phase
-- exponent (-a² + 4a - 2)/(8a).
M-Z-exponent : ℤ* ₚ → ℤ ₚ
M-Z-exponent a* = (₁ + - a) * 1/2 * a⁻¹
  where
  a = a* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁

M-phase : ℤ* ₚ → ℤ ₚ
M-phase a* = (- (a * a) + (₂ + ₂) * a + - ₂) * 1/8 * a⁻¹
  where
  a = a* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁

M : ℤ* ₚ → Word (Gen (₁₊ n))
M a* =
  Z^ (M-Z-exponent a*) • X^ ((₁ + - a) * 1/2)
  • S^ a⁻¹ • H • S^ a • H • S^ a⁻¹ • H
  • legendre a* • ω^ (M-phase a*)
  where
  a = a* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁

-- The two multipliers the rules name.
Mg : Word (Gen (₁₊ n))
Mg = M g′

M₋₁ : Word (Gen (₁₊ n))
M₋₁ = M -'₁

-- T4: the swap, three CZs between Hadamard layers, and the phase λ_p².
SWAP : Word (Gen (₂₊ n))
SWAP = CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • λ²

-- T5: CNOT, controlled on the top wire.
CX : Word (Gen (₂₊ n))
CX = H ↓ ^ 3 • CZ • H ↓

-- T7: the remote CZ between the top and bottom of three wires.
CIZ : Word (Gen (₃₊ n))
CIZ = SWAP • CZ ↑ • SWAP

------------------------------------------------------------------------
-- The rules of Figure 1

-- The inverse of the primitive root, which C4 squares.
g⁻¹ : ℤ ₚ
g⁻¹ = (g′ ⁻¹) .proj₁

infix 4 _Fig1,_===_

data _Fig1,_===_ : (n : ℕ) → CRel n where

  -- One scalar rule, at every width.
  c0  : n Fig1,  ν ^ (p Nat.+ p) === ε

  -- Single qudit.
  c1  : (₁₊ n) Fig1,  S ^ p === ε
  c2  : (₁₊ n) Fig1,  H ^ 2 === M₋₁ • -1ˢ ^ p-1/2
  c3  : ∀ (k : ℤ ₚ) → (₁₊ n) Fig1,  Mg ^ toℕ k === M (g^ k)
  c4  : (₁₊ n) Fig1,
          Mg • S === Z^ ((₁ + - g) * 1/2 * (g⁻¹ * g⁻¹)) • S^ (g⁻¹ * g⁻¹) • Mg
  c5  : (₁₊ n) Fig1,  S • H • H • S • H • H === H • H • S • H • H • S

  -- Two qudits.
  c6  : (₂₊ n) Fig1,  CZ ^ p === ε
  c7  : (₂₊ n) Fig1,  SWAP • SWAP === ε
  c8  : (₂₊ n) Fig1,  CZ • S ↑ === S ↑ • CZ
  c9  : (₂₊ n) Fig1,  CZ • Mg ↑ === Mg ↑ • CZ^ g
  c10 : (₂₊ n) Fig1,  SWAP • S ↑ === S ↓ • SWAP
  c11 : (₂₊ n) Fig1,  SWAP • H ↑ === H ↓ • SWAP
  c12 : (₂₊ n) Fig1,
          (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX === CZ

  -- Three qudits.
  c13 : (₃₊ n) Fig1,
          SWAP ↑ • SWAP ↓ • SWAP ↑ === SWAP ↓ • SWAP ↑ • SWAP ↓
  c14 : (₃₊ n) Fig1,  SWAP ↓ • SWAP ↑ • CZ ↓ === CZ ↑ • SWAP ↓ • SWAP ↑
  c15 : (₃₊ n) Fig1,  CZ ↓ • CX ↑ === CIZ • CX ↑ • CZ ↓

------------------------------------------------------------------------
-- The full relation
--
-- The rules above together with the structural rules every circuit
-- presentation has: cong↑, comm₁ and comm₂ (gates on disjoint wires
-- commute) and ω↑=ω (ν is the same on every wire).  That ν is central
-- is Circuit.Base's theorem comm₀, which asks only that scalars commute
-- with one another: here there is one.

open Lift-Relation _Fig1,_===_ public
open Central-Scalars (λ { ν-gate ν-gate → PB.refl }) public
  using (comm₀ ; comm-gate₀-w)

infix 4 _F,_===_
_F,_===_ : (n : ℕ) → CRel n
_F,_===_ = _VRel,_===_

infix 4 _≈ᶠ_
_≈ᶠ_ : {n : ℕ} → Word (Gen n) → Word (Gen n) → Set
_≈ᶠ_ {n} = PB._≈_ (n F,_===_)

------------------------------------------------------------------------
-- The scalar is central, and the same on every wire
--
-- Both from the structural rules, walked across a word.

ν-central : (w : Word (Gen n)) → (ν • w) ≈ᶠ (w • ν)
ν-central [ y ]ʷ  = PB.sym (comm₀ ν-gate y)
ν-central ε       = PB.trans PB.right-unit (PB.sym PB.left-unit)
ν-central (w • v) =
  PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (ν-central w) PB.refl)
      (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl (ν-central v)) (PB.sym PB.assoc))))

ν^-central : (k : ℕ) (w : Word (Gen n)) → ((ν ^ k) • w) ≈ᶠ (w • (ν ^ k))
ν^-central ₀       w = PB.trans PB.left-unit (PB.sym PB.right-unit)
ν^-central (₁₊ ₀)  w = ν-central w
ν^-central (₂₊ k)  w =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (ν^-central (₁₊ k) w))
      (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (ν-central w) PB.refl) PB.assoc)))

ν↑≈ν : ((ν {n}) ↑) ≈ᶠ ν
ν↑≈ν = PB.axiom (ω↑=ω ν-gate)
