------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1's C4 and Paper-V1's semi-MR derive each other.
--
-- Both rules say how the multiplier M_g conjugates S.  Paper-V1 (and
-- Gates' simplified rule set before it) conjugates by M_g⁻¹,
--
--     semi-MR :  W • S^(g²) • Z^e  ≈  S • W,      e = (g² - g)·½,
--
-- and Figure 1 of arXiv:2609.40106 conjugates by M_g,
--
--     semi-MS :  W • S  ≈  Z^c • S^d • W,         c = (1 - g)·½·d,
--                                                 d = g⁻²,
--
-- where W is the multiplier word.  Read as operators both are true,
-- and each follows from the other given one more fact, that W
-- conjugates Z to Z^g:
--
--     Z-W :  Z^k • W  ≈  W • Z^(g·k).
--
-- semi-MS ⇒ semi-MR: iterate semi-MS g² times, collapse the S-power
-- with g⁻² · g² = 1, and carry the Z^e on the left across W.  The
-- converse iterates semi-MR g⁻² times instead.  Everything else is the
-- Pauli bookkeeping of ℤₚ-indexed powers, and four identities in ℤₚ.
--
-- Stated over an abstract relation Γ, so that the same proof runs at
-- Figure 1 mod scalars (semi-MS ⇒ semi-MR) and at Paper-V1
-- (semi-MR ⇒ semi-MS); the facts it needs are what both lemma
-- libraries already have, and Z-W is their Z-XM.
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

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.SemiMS
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Nat.DivMod using (_%_)
import Data.Nat as Nat
open import Data.Product using (proj₁)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; WRel ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP

open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime using (toℕ-+)

open Primitive-Root-Modp' g* g-gen using (g′)

open import Examples.Groups.Symplectic.Simplified.Syntactics
  p-2 p-prime g* g-gen as NSim
open NSim.Symplectic using (Gen ; S)

import Examples.Groups.ProjectiveClifford.Qupit.Shared.PauliBase
  p-3 p-prime g* g-gen as Shared
open Shared using (Z ; Z^ ; S^' ; 1/2 ; neg-*)

------------------------------------------------------------------------
-- The exponents

-- g⁻¹, written u below.
g⁻¹ : ℤ ₚ
g⁻¹ = (g′ ⁻¹) .proj₁

-- g⁻², the S-exponent of semi-MS.
d : ℤ ₚ
d = g⁻¹ * g⁻¹

-- The Z-exponent of semi-MS.
c : ℤ ₚ
c = (₁ + - g) * 1/2 * d

-- The Z-exponent of semi-MR.
e : ℤ ₚ
e = (g * g + - g) * 1/2

------------------------------------------------------------------------
-- Four identities in ℤₚ
--
-- Each is ring arithmetic plus g · g⁻¹ = 1.  They are spelled out step
-- by step: the ring solver cannot combine like terms here, since a
-- coefficient such as -1 + 1 does not reduce when p is a variable.

module Arith where

  open Eq.≡-Reasoning

  private
    gu : g * g⁻¹ ≡ ₁
    gu = lemma-⁻¹ʳ g {{nztoℕ {y = g} {neq0 = g≠0}}}

    ug : g⁻¹ * g ≡ ₁
    ug = lemma-⁻¹ˡ g {{nztoℕ {y = g} {neq0 = g≠0}}}


    -- Two units multiply to a unit: (xy)(zw) with xz = yw = 1.
    swap4 : ∀ (x y z w : ℤ ₚ) → (x * y) * (z * w) ≡ (x * z) * (y * w)
    swap4 x y z w = begin
      (x * y) * (z * w)  ≡⟨ *-assoc x y (z * w) ⟩
      x * (y * (z * w))  ≡⟨ Eq.cong (x *_) (Eq.sym (*-assoc y z w)) ⟩
      x * ((y * z) * w)  ≡⟨ Eq.cong (λ t → x * (t * w)) (*-comm y z) ⟩
      x * ((z * y) * w)  ≡⟨ Eq.cong (x *_) (*-assoc z y w) ⟩
      x * (z * (y * w))  ≡⟨ Eq.sym (*-assoc x z (y * w)) ⟩
      (x * z) * (y * w)  ∎

    -- -x + x = 0, and the sum of a difference and its opposite.
    cancel-pair : ∀ (x y : ℤ ₚ) → (x + - y) + (y + - x) ≡ ₀
    cancel-pair x y = begin
      (x + - y) + (y + - x)  ≡⟨ +-assoc x (- y) (y + - x) ⟩
      x + (- y + (y + - x))  ≡⟨ Eq.cong (x +_) (Eq.sym (+-assoc (- y) y (- x))) ⟩
      x + ((- y + y) + - x)  ≡⟨ Eq.cong (λ t → x + (t + - x)) (+-inverseˡ y) ⟩
      x + (₀ + - x)          ≡⟨ Eq.cong (x +_) (+-identityˡ (- x)) ⟩
      x + - x                ≡⟨ +-inverseʳ x ⟩
      ₀                      ∎

    -- (a - b)·w = a·w - b·w.
    sub-distribʳ : ∀ (a b w : ℤ ₚ) → (a + - b) * w ≡ a * w + - (b * w)
    sub-distribʳ a b w = begin
      (a + - b) * w        ≡⟨ *-distribʳ-+ w a (- b) ⟩
      a * w + (- b) * w    ≡⟨ Eq.cong (a * w +_) (neg-* b w) ⟩
      a * w + - (b * w)    ∎

  -- R1: g⁻² · g² = 1, either way round.
  d·gg : d * (g * g) ≡ ₁
  d·gg = begin
    (g⁻¹ * g⁻¹) * (g * g)  ≡⟨ swap4 g⁻¹ g⁻¹ g g ⟩
    (g⁻¹ * g) * (g⁻¹ * g)  ≡⟨ Eq.cong₂ _*_ ug ug ⟩
    ₁ * ₁                  ≡⟨ *-identityˡ ₁ ⟩
    ₁                      ∎

  gg·d : (g * g) * d ≡ ₁
  gg·d = Eq.trans (*-comm (g * g) d) d·gg

  -- R3: g undoes g⁻¹.
  g·[x·u] : ∀ (x : ℤ ₚ) → g * (x * g⁻¹) ≡ x
  g·[x·u] x = begin
    g * (x * g⁻¹)   ≡⟨ Eq.cong (g *_) (*-comm x g⁻¹) ⟩
    g * (g⁻¹ * x)   ≡⟨ Eq.sym (*-assoc g g⁻¹ x) ⟩
    (g * g⁻¹) * x   ≡⟨ Eq.cong (_* x) gu ⟩
    ₁ * x           ≡⟨ *-identityˡ x ⟩
    x               ∎

  private
    -- c · g² = (1 - g)·½ and e · g⁻¹ = (g - 1)·½.
    c·gg : c * (g * g) ≡ (₁ + - g) * 1/2
    c·gg = begin
      ((₁ + - g) * 1/2) * d * (g * g)    ≡⟨ *-assoc ((₁ + - g) * 1/2) d (g * g) ⟩
      ((₁ + - g) * 1/2) * (d * (g * g))  ≡⟨ Eq.cong (((₁ + - g) * 1/2) *_) d·gg ⟩
      ((₁ + - g) * 1/2) * ₁              ≡⟨ *-identityʳ ((₁ + - g) * 1/2) ⟩
      (₁ + - g) * 1/2                    ∎

    e·u : e * g⁻¹ ≡ (g + - ₁) * 1/2
    e·u = begin
      ((g * g + - g) * 1/2) * g⁻¹     ≡⟨ *-assoc (g * g + - g) 1/2 g⁻¹ ⟩
      (g * g + - g) * (1/2 * g⁻¹)     ≡⟨ Eq.cong ((g * g + - g) *_) (*-comm 1/2 g⁻¹) ⟩
      (g * g + - g) * (g⁻¹ * 1/2)     ≡⟨ Eq.sym (*-assoc (g * g + - g) g⁻¹ 1/2) ⟩
      ((g * g + - g) * g⁻¹) * 1/2     ≡⟨ Eq.cong (_* 1/2) inner ⟩
      (g + - ₁) * 1/2                 ∎
      where
      inner : (g * g + - g) * g⁻¹ ≡ g + - ₁
      inner = begin
        (g * g + - g) * g⁻¹       ≡⟨ sub-distribʳ (g * g) g g⁻¹ ⟩
        g * g * g⁻¹ + - (g * g⁻¹) ≡⟨ Eq.cong₂ (λ s t → s + - t)
                                      (Eq.trans (*-assoc g g g⁻¹)
                                        (Eq.trans (Eq.cong (g *_) gu) (*-identityʳ g)))
                                      gu ⟩
        g + - ₁                   ∎

  -- R2: the Z-exponents of the two derivations cancel.
  c·gg+e·u : c * (g * g) + e * g⁻¹ ≡ ₀
  c·gg+e·u = begin
    c * (g * g) + e * g⁻¹                  ≡⟨ Eq.cong₂ _+_ c·gg e·u ⟩
    (₁ + - g) * 1/2 + (g + - ₁) * 1/2      ≡⟨ Eq.sym (*-distribʳ-+ 1/2 (₁ + - g) (g + - ₁)) ⟩
    ((₁ + - g) + (g + - ₁)) * 1/2          ≡⟨ Eq.cong (_* 1/2) (cancel-pair ₁ g) ⟩
    ₀ * 1/2                                ≡⟨ *-zeroˡ 1/2 ⟩
    ₀                                      ∎

  -- R4: - (e · g⁻²) · g⁻¹ is c.
  -[e·d]·u : - (e * d) * g⁻¹ ≡ c
  -[e·d]·u = begin
    - (e * d) * g⁻¹              ≡⟨ neg-* (e * d) g⁻¹ ⟩
    - (e * d * g⁻¹)              ≡⟨ Eq.cong -_ ed-u ⟩
    - ((g⁻¹ + - d) * 1/2)        ≡⟨ Eq.sym (neg-* (g⁻¹ + - d) 1/2) ⟩
    (- (g⁻¹ + - d)) * 1/2        ≡⟨ Eq.cong (_* 1/2) (neg-sub g⁻¹ d) ⟩
    (d + - g⁻¹) * 1/2            ≡⟨ Eq.sym c-alt ⟩
    c                            ∎
    where
    -- e · g⁻² · g⁻¹ = (g⁻¹ - g⁻²)·½, by e · g⁻¹ = (g - 1)·½ and g·g⁻² = g⁻¹.
    g·d : g * d ≡ g⁻¹
    g·d = Eq.trans (Eq.sym (*-assoc g g⁻¹ g⁻¹))
            (Eq.trans (Eq.cong (_* g⁻¹) gu) (*-identityˡ g⁻¹))

    ed-u : e * d * g⁻¹ ≡ (g⁻¹ + - d) * 1/2
    ed-u = begin
      e * d * g⁻¹               ≡⟨ *-assoc e d g⁻¹ ⟩
      e * (d * g⁻¹)             ≡⟨ Eq.cong (e *_) (*-comm d g⁻¹) ⟩
      e * (g⁻¹ * d)             ≡⟨ Eq.sym (*-assoc e g⁻¹ d) ⟩
      e * g⁻¹ * d               ≡⟨ Eq.cong (_* d) e·u ⟩
      (g + - ₁) * 1/2 * d       ≡⟨ *-assoc (g + - ₁) 1/2 d ⟩
      (g + - ₁) * (1/2 * d)     ≡⟨ Eq.cong ((g + - ₁) *_) (*-comm 1/2 d) ⟩
      (g + - ₁) * (d * 1/2)     ≡⟨ Eq.sym (*-assoc (g + - ₁) d 1/2) ⟩
      (g + - ₁) * d * 1/2       ≡⟨ Eq.cong (_* 1/2) (sub-distribʳ g ₁ d) ⟩
      (g * d + - (₁ * d)) * 1/2 ≡⟨ Eq.cong₂ (λ s t → (s + - t) * 1/2) g·d (*-identityˡ d) ⟩
      (g⁻¹ + - d) * 1/2         ∎

    -- - (x - y) = y - x.
    neg-sub : ∀ (x y : ℤ ₚ) → - (x + - y) ≡ y + - x
    neg-sub x y = begin
      - (x + - y)      ≡⟨ Shared.neg-+ x (- y) ⟩
      - x + - (- y)    ≡⟨ Eq.cong (- x +_) (Shared.neg-involutive y) ⟩
      - x + y          ≡⟨ +-comm (- x) y ⟩
      y + - x          ∎

    -- c, rewritten: (1 - g)·½·g⁻² = (g⁻² - g⁻¹)·½.
    c-alt : c ≡ (d + - g⁻¹) * 1/2
    c-alt = begin
      (₁ + - g) * 1/2 * d        ≡⟨ *-assoc (₁ + - g) 1/2 d ⟩
      (₁ + - g) * (1/2 * d)      ≡⟨ Eq.cong ((₁ + - g) *_) (*-comm 1/2 d) ⟩
      (₁ + - g) * (d * 1/2)      ≡⟨ Eq.sym (*-assoc (₁ + - g) d 1/2) ⟩
      (₁ + - g) * d * 1/2        ≡⟨ Eq.cong (_* 1/2) (sub-distribʳ ₁ g d) ⟩
      (₁ * d + - (g * d)) * 1/2  ≡⟨ Eq.cong₂ (λ s t → (s + - t) * 1/2) (*-identityˡ d) g·d ⟩
      (d + - g⁻¹) * 1/2          ∎

open Arith public
  using (d·gg ; gg·d ; g·[x·u] ; c·gg+e·u ; -[e·d]·u)

------------------------------------------------------------------------
-- The two derivations, over an abstract relation

module Conversion
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (W : Word (Gen (₁₊ n)))
  (order-S : let open PB Γ in S ^ p ≈ ε)
  (order-Z : let open PB Γ in Z ^ p ≈ ε)
  (comm-Z-S : let open PB Γ in Z • S ≈ S • Z)
  (pow-mod : let open PB Γ in
             ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ m → w ^ m ≈ w ^ (m % p))
  (Z-W : let open PB Γ in ∀ k → Z^ k • W ≈ W • Z^ (g * k))
  where

  open PB Γ
  open PP Γ
  open SR word-setoid

  --------------------------------------------------------------------
  -- Powers at ℤₚ exponents

  private
    pow-+ : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ (a b : ℤ ₚ) →
            w ^ toℕ a • w ^ toℕ b ≈ w ^ toℕ (a + b)
    pow-+ w ord a b = begin
      w ^ toℕ a • w ^ toℕ b          ≈⟨ sym (^-+ w (toℕ a) (toℕ b)) ⟩
      w ^ (toℕ a Nat.+ toℕ b)        ≈⟨ pow-mod w ord (toℕ a Nat.+ toℕ b) ⟩
      w ^ ((toℕ a Nat.+ toℕ b) % p)  ≈⟨ refl' (Eq.cong (w ^_) (Eq.sym (toℕ-+ a b))) ⟩
      w ^ toℕ (a + b)                ∎

    pow-* : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ (a b : ℤ ₚ) →
            (w ^ toℕ a) ^ toℕ b ≈ w ^ toℕ (a * b)
    pow-* w ord a b = begin
      (w ^ toℕ a) ^ toℕ b            ≈⟨ ^^ w (toℕ a) (toℕ b) ⟩
      w ^ (toℕ a Nat.* toℕ b)        ≈⟨ pow-mod w ord _ ⟩
      w ^ ((toℕ a Nat.* toℕ b) % p)  ≈⟨ refl' (Eq.cong (w ^_) (lemma-toℕ-% a b)) ⟩
      w ^ toℕ (a * b)                ∎

  Z^-+ : ∀ a b → Z^ a • Z^ b ≈ Z^ (a + b)
  Z^-+ = pow-+ Z order-Z

  Z^-* : ∀ a b → (Z^ a) ^ toℕ b ≈ Z^ (a * b)
  Z^-* = pow-* Z order-Z

  S^-* : ∀ a b → (S^' a) ^ toℕ b ≈ S^' (a * b)
  S^-* = pow-* S order-S

  comm-Z^-S^ : ∀ a b → Z^ a • S^' b ≈ S^' b • Z^ a
  comm-Z^-S^ a b = comm⇒pow-comm (toℕ a) (toℕ b) comm-Z-S

  -- A Z-power past W, the other way: W • Z^x ≈ Z^(x·g⁻¹) • W.
  W-Z : ∀ x → W • Z^ x ≈ Z^ (x * g⁻¹) • W
  W-Z x = begin
    W • Z^ x                  ≡⟨ Eq.cong (λ t → W • Z^ t) (Eq.sym (g·[x·u] x)) ⟩
    W • Z^ (g * (x * g⁻¹))    ≈⟨ sym (Z-W (x * g⁻¹)) ⟩
    Z^ (x * g⁻¹) • W          ∎

  -- Z^x • Z^(-x) is ε.
  Z^-cancel : ∀ x → Z^ x • Z^ (- x) ≈ ε
  Z^-cancel x = trans (Z^-+ x (- x)) (refl' (Eq.cong (λ t → Z^ t) (+-inverseʳ x)))

  --------------------------------------------------------------------
  -- Iterating a conjugation

  private
    induction : ∀ {a b c'} → a • b ≈ c' • a → ∀ k → a • b ^ k ≈ c' ^ k • a
    induction eq ₀      = trans right-unit (sym left-unit)
    induction eq (₁₊ ₀) = eq
    induction {a} {b} {c'} eq (₂₊ k) = begin
      a • (b • b ^ ₁₊ k)    ≈⟨ sym assoc ⟩
      (a • b) • b ^ ₁₊ k    ≈⟨ cleft eq ⟩
      (c' • a) • b ^ ₁₊ k   ≈⟨ assoc ⟩
      c' • (a • b ^ ₁₊ k)   ≈⟨ cright induction eq (₁₊ k) ⟩
      c' • (c' ^ ₁₊ k • a)  ≈⟨ sym assoc ⟩
      (c' • c' ^ ₁₊ k) • a  ∎

    inductionˡ : ∀ {a b c'} → a • b ≈ b • c' → ∀ k → a ^ k • b ≈ b • c' ^ k
    inductionˡ eq ₀      = trans left-unit (sym right-unit)
    inductionˡ eq (₁₊ ₀) = eq
    inductionˡ {a} {b} {c'} eq (₂₊ k) = begin
      (a • a ^ ₁₊ k) • b    ≈⟨ assoc ⟩
      a • (a ^ ₁₊ k • b)    ≈⟨ cright inductionˡ eq (₁₊ k) ⟩
      a • (b • c' ^ ₁₊ k)   ≈⟨ sym assoc ⟩
      (a • b) • c' ^ ₁₊ k   ≈⟨ cleft eq ⟩
      (b • c') • c' ^ ₁₊ k  ≈⟨ assoc ⟩
      b • (c' • c' ^ ₁₊ k)  ∎

  --------------------------------------------------------------------
  -- semi-MS ⇒ semi-MR

  MS⇒MR : W • S ≈ Z^ c • (S^' d • W) → W • (S^' (g * g) • Z^ e) ≈ S • W
  MS⇒MR ms = begin
    W • (S^' (g * g) • Z^ e)                ≈⟨ sym assoc ⟩
    (W • S^' (g * g)) • Z^ e                ≈⟨ cleft iterated ⟩
    ((Z^ c' • S) • W) • Z^ e                ≈⟨ assoc ⟩
    (Z^ c' • S) • (W • Z^ e)                ≈⟨ cright W-Z e ⟩
    (Z^ c' • S) • (Z^ (e * g⁻¹) • W)        ≈⟨ assoc ⟩
    Z^ c' • (S • (Z^ (e * g⁻¹) • W))        ≈⟨ cright sym assoc ⟩
    Z^ c' • ((S • Z^ (e * g⁻¹)) • W)        ≈⟨ cright cleft sym (comm-Z^-S^ (e * g⁻¹) ₁) ⟩
    Z^ c' • ((Z^ (e * g⁻¹) • S) • W)        ≈⟨ cright assoc ⟩
    Z^ c' • (Z^ (e * g⁻¹) • (S • W))        ≈⟨ sym assoc ⟩
    (Z^ c' • Z^ (e * g⁻¹)) • (S • W)        ≈⟨ cleft Z^-+ c' (e * g⁻¹) ⟩
    Z^ (c' + e * g⁻¹) • (S • W)             ≡⟨ Eq.cong (λ t → Z^ t • (S • W)) c·gg+e·u ⟩
    ε • (S • W)                             ≈⟨ left-unit ⟩
    S • W                                   ∎
    where
    c' : ℤ ₚ
    c' = c * (g * g)

    -- semi-MS, iterated g² times.
    iterated : W • S^' (g * g) ≈ (Z^ c' • S) • W
    iterated = begin
      W • S ^ toℕ (g * g)
        ≈⟨ induction (trans ms (sym assoc)) (toℕ (g * g)) ⟩
      (Z^ c • S^' d) ^ toℕ (g * g) • W
        ≈⟨ cleft ^-• (Z^ c) (S^' d) (toℕ (g * g)) (comm-Z^-S^ c d) ⟩
      ((Z^ c) ^ toℕ (g * g) • (S^' d) ^ toℕ (g * g)) • W
        ≈⟨ cleft cong (Z^-* c (g * g)) (S^-* d (g * g)) ⟩
      (Z^ c' • S^' (d * (g * g))) • W
        ≡⟨ Eq.cong (λ t → (Z^ c' • S^' t) • W) d·gg ⟩
      (Z^ c' • S) • W
        ∎

  --------------------------------------------------------------------
  -- semi-MR ⇒ semi-MS

  MR⇒MS : W • (S^' (g * g) • Z^ e) ≈ S • W → W • S ≈ Z^ c • (S^' d • W)
  MR⇒MS mr = begin
    W • S                                   ≈⟨ sym right-unit ⟩
    (W • S) • ε                             ≈⟨ cright sym (Z^-cancel f) ⟩
    (W • S) • (Z^ f • Z^ (- f))             ≈⟨ sym assoc ⟩
    ((W • S) • Z^ f) • Z^ (- f)             ≈⟨ cleft assoc ⟩
    (W • (S • Z^ f)) • Z^ (- f)             ≈⟨ cleft sym iterated ⟩
    (S^' d • W) • Z^ (- f)                  ≈⟨ assoc ⟩
    S^' d • (W • Z^ (- f))                  ≈⟨ cright W-Z (- f) ⟩
    S^' d • (Z^ (- f * g⁻¹) • W)            ≡⟨ Eq.cong (λ t → S^' d • (Z^ t • W)) -[e·d]·u ⟩
    S^' d • (Z^ c • W)                      ≈⟨ sym assoc ⟩
    (S^' d • Z^ c) • W                      ≈⟨ cleft sym (comm-Z^-S^ c d) ⟩
    (Z^ c • S^' d) • W                      ≈⟨ assoc ⟩
    Z^ c • (S^' d • W)                      ∎
    where
    f : ℤ ₚ
    f = e * d

    -- semi-MR, iterated g⁻² times.
    iterated : S^' d • W ≈ W • (S • Z^ f)
    iterated = begin
      S ^ toℕ d • W
        ≈⟨ inductionˡ (sym mr) (toℕ d) ⟩
      W • (S^' (g * g) • Z^ e) ^ toℕ d
        ≈⟨ cright ^-• (S^' (g * g)) (Z^ e) (toℕ d) (sym (comm-Z^-S^ e (g * g))) ⟩
      W • ((S^' (g * g)) ^ toℕ d • (Z^ e) ^ toℕ d)
        ≈⟨ cright cong (S^-* (g * g) d) (Z^-* e d) ⟩
      W • (S^' ((g * g) * d) • Z^ f)
        ≡⟨ Eq.cong (λ t → W • (S^' t • Z^ f)) gg·d ⟩
      W • (S • Z^ f)
        ∎
