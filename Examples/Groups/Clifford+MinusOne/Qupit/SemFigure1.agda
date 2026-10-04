------------------------------------------------------------------------
-- Presentations of groups
--
-- The phase of Figure 1's multiplier.
--
-- Figure 1 (T1) writes the multiplier as a gate word followed by two
-- scalars,
--
--     M_a = Z^γ X^δ S^(a⁻¹) H S^a H S^(a⁻¹) H · (a/p)_L · ω^(M-phase a),
--
--     γ = (a⁻¹ - 1)·½,  δ = (1 - a)·½,
--     M-phase a = (-a² + 4a - 2)/(8a),
--
-- and the gate word in front is Figure1.ModScalar's XM a.  Read in the
-- exact Clifford group with the Weyl cocycle (Clifford.Qupit.SemRealises),
-- XM a picks up the phase ω^(-M-phase a): exactly the power of ω that
-- T1 appends cancels it.  This file proves that, and the facts about Φ
-- that the rules mentioning the multiplier then need.
--
-- How.  Clifford.Qupit.SemLocal reads a one-wire word as a triple — a
-- Pauli (x , z), a matrix (a b ; c d) and the phase φ — and multiplies
-- triples by the Heisenberg–Weyl law.  Over S rather than SemLocal's R
-- the multiplier is NOT phase-free, and its triple is computed here
-- letter by letter, the word read from the right:
--
--     H, S^b, H, S^a, H, S^b      Pauli ends at ((a - 1)·½ , b(a - 1)·½)
--     X^δ, Z^γ                    ... which these two cancel,
--
-- with b = a⁻¹, leaving the pure multiplier diag(a , a⁻¹) and the phase
--
--     ½·[(b½)(a σ) + ((a - 1)½)(b σ) + (-δ)(b(a - 1)½)]  =  -M-phase a,
--
-- σ = -½ being the Pauli S carries.  Each step is normalised before the
-- next (has-≡), so no coefficient ever grows; the phase is left as the
-- sum of its three cocycle terms and settled once at the end (Arith).
--
-- What comes out.
--
--   * has-X, has-X^' : X^y is the Pauli (y , 0) with no phase;
--   * has-XM, Φ-XM   : XM a has no Pauli, matrix diag(a , a⁻¹) and phase
--                      -M-phase a;
--   * Φ-XM^          : its powers, whose phases simply add;
--   * Φ-semi-MS      : the two sides of Figure 1's C4 (semi-MS) carry the
--                      same phase, that of XMg;
--   * Φ-H²           : H² is phase-free.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.SemFigure1
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Product using (proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Algebra.Properties.Ring (+-*-ring p-2)
  using ( -0#≈0# ; -‿+-comm ; -‿involutive
        ; -‿distribˡ-* ; -‿distribʳ-* ; [-x][-y]≈xy )
import Algebra.Solver.CommutativeMonoid as CMSolver
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
  using (mult ; mult-toℕ)

open import Word.Base using (_•_ ; _^_)

open Primitive-Root-Modp' g* g-gen using (g′)

import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS
import Examples.Groups.Clifford.Qupit.SemLocal
  p-3 p-prime g* g-gen as SL
import Examples.Groups.Clifford.Qupit.SemRealises
  p-3 p-prime g* g-gen as RL
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen as F
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Syntactics
  p-3 p-prime g* g-gen as FQ
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.SemiMS
  p-3 p-prime g* g-gen as SMS

open FQ using (H ; S ; S^ ; S⁻¹ ; 1/2)
open FQ.Clifford-Relations
  using (X ; X^ ; Z^ ; SHS' ; XM ; XMg ; XMg^ ; g⁻¹)
open SL using (h ; σ ; σ+σ)

------------------------------------------------------------------------
-- Ring lemmas
--
-- The ring solver is used only where no two monomials meet (`r1`–`r4`
-- below): with p a variable, a coefficient such as -1 + 1 does not
-- reduce, so every cancellation is spelled out by hand.  The one
-- rearrangement of a long sum goes through the commutative-monoid
-- solver instead, which counts atoms in ℕ and never sees a coefficient.

private
  oz : ∀ (x y : ℤ ₚ) → ₁ * x + ₀ * y ≡ x
  oz x y = Eq.trans (Eq.cong₂ _+_ (*-identityˡ x) (*-zeroˡ y)) (+-identityʳ x)

  zo : ∀ (x y : ℤ ₚ) → ₀ * x + ₁ * y ≡ y
  zo x y = Eq.trans (Eq.cong₂ _+_ (*-zeroˡ x) (*-identityˡ y)) (+-identityˡ y)

  negzero : ∀ (y : ℤ ₚ) → (- ₀) * y ≡ ₀
  negzero y = Eq.trans (Eq.cong (_* y) -0#≈0#) (*-zeroˡ y)

  neg-* : ∀ (x y : ℤ ₚ) → (- x) * y ≡ - (x * y)
  neg-* x y = Eq.sym (-‿distribˡ-* x y)

  *-neg : ∀ (x y : ℤ ₚ) → x * (- y) ≡ - (x * y)
  *-neg x y = Eq.sym (-‿distribʳ-* x y)

  *-neg₁ : ∀ (x : ℤ ₚ) → x * (- ₁) ≡ - x
  *-neg₁ x = Eq.trans (*-neg x ₁) (Eq.cong -_ (*-identityʳ x))

  mm : (- ₁) * (- ₁) ≡ ₁
  mm = Eq.trans ([-x][-y]≈xy ₁ ₁) (*-identityˡ ₁)

  -- A cocycle term whose left factor vanishes.
  h0 : ∀ (y : ℤ ₚ) → h * (₀ * y) ≡ ₀
  h0 y = Eq.trans (Eq.cong (h *_) (*-zeroˡ y)) (*-zeroʳ h)

  -- ₀ + h·(₀·y) = ₀.
  0h0 : ∀ (y : ℤ ₚ) → ₀ + h * (₀ * y) ≡ ₀
  0h0 y = Eq.trans (+-identityˡ _) (h0 y)

  -- A difference and its opposite cancel.
  cancel-pair : ∀ (x y : ℤ ₚ) → (x + - y) + (y + - x) ≡ ₀
  cancel-pair x y = begin
    (x + - y) + (y + - x)  ≡⟨ +-assoc x (- y) (y + - x) ⟩
    x + (- y + (y + - x))  ≡⟨ Eq.cong (x +_) (Eq.sym (+-assoc (- y) y (- x))) ⟩
    x + ((- y + y) + - x)  ≡⟨ Eq.cong (λ t → x + (t + - x)) (+-inverseˡ y) ⟩
    x + (₀ + - x)          ≡⟨ Eq.cong (x +_) (+-identityˡ (- x)) ⟩
    x + - x                ≡⟨ +-inverseʳ x ⟩
    ₀                      ∎

  -- ... and so do their multiples.
  cancel-pair* : ∀ (x y k : ℤ ₚ) → (x + - y) * k + (y + - x) * k ≡ ₀
  cancel-pair* x y k =
    Eq.trans (Eq.sym (*-distribʳ-+ k (x + - y) (y + - x)))
      (Eq.trans (Eq.cong (_* k) (cancel-pair x y)) (*-zeroˡ k))

------------------------------------------------------------------------
-- The phase identity
--
-- In terms of an arbitrary k (in use, the cocycle's ½), with
-- u = a - 1 and v = 1 - a, the three cocycle terms the multiplier
-- accumulates are -k³·ab, -k³·ub and -k³·vub.  Their sum is
-- -k³·(a + u + vu)·b, and a + u + vu is -a² + 4a - 2 as a polynomial in
-- a (`core`) — so the identity holds in any commutative ring, without
-- ab = 1 and without 2k = 1.

module Arith where

  private
    module CM = CMSolver
      (CommutativeRing.+-commutativeMonoid (+-*-commutativeRing p-2))

    -- Pure rearrangements: every monomial occurs once on each side.
    r1 : ∀ (a b k : ℤ ₚ) → k * ((b * k) * (a * k)) ≡ k * k * k * (a * b)
    r1 = solve p-2 3
      (λ a b k → (k ⊗ ((b ⊗ k) ⊗ (a ⊗ k))) , (((k ⊗ k) ⊗ k) ⊗ (a ⊗ b)))
      (λ {_} {_} {_} → Eq.refl)

    r2 : ∀ (u b k : ℤ ₚ) → k * ((u * k) * (b * k)) ≡ k * k * k * (u * b)
    r2 = solve p-2 3
      (λ u b k → (k ⊗ ((u ⊗ k) ⊗ (b ⊗ k))) , (((k ⊗ k) ⊗ k) ⊗ (u ⊗ b)))
      (λ {_} {_} {_} → Eq.refl)

    r3 : ∀ (v b u k : ℤ ₚ) →
         k * ((v * k) * (b * (u * k))) ≡ k * k * k * ((v * u) * b)
    r3 = solve p-2 4
      (λ v b u k → (k ⊗ ((v ⊗ k) ⊗ (b ⊗ (u ⊗ k)))) ,
                   (((k ⊗ k) ⊗ k) ⊗ ((v ⊗ u) ⊗ b)))
      (λ {_} {_} {_} {_} → Eq.refl)

    r4 : ∀ (a u w b k : ℤ ₚ) →
         (k * k * k * (a * b) + k * k * k * (u * b)) + k * k * k * (w * b)
           ≡ ((a + u) + w) * (k * k * k) * b
    r4 = solve p-2 5
      (λ a u w b k →
         ((((k ⊗ k) ⊗ k) ⊗ (a ⊗ b)) ⊕ (((k ⊗ k) ⊗ k) ⊗ (u ⊗ b)))
           ⊕ (((k ⊗ k) ⊗ k) ⊗ (w ⊗ b)) ,
         ((((a ⊕ u) ⊕ w) ⊗ ((k ⊗ k) ⊗ k)) ⊗ b))
      (λ {_} {_} {_} {_} {_} → Eq.refl)

    -- 2·a = a + a and 4·a = (a + a) + (a + a).  (₁ + ₁ reduces to ₂, as
    -- p ≥ 3; it is ₂ + ₁ that would not.)
    two-a : ∀ (a : ℤ ₚ) → ₂ * a ≡ a + a
    two-a a = Eq.trans (*-distribʳ-+ a ₁ ₁)
                       (Eq.cong₂ _+_ (*-identityˡ a) (*-identityˡ a))

    four-a : ∀ (a : ℤ ₚ) → (₂ + ₂) * a ≡ (a + a) + (a + a)
    four-a a = Eq.trans (*-distribʳ-+ a ₂ ₂) (Eq.cong₂ _+_ (two-a a) (two-a a))

    -- (1 - a)(a - 1) = (a - 1) + (-a² + a).
    vu : ∀ (a : ℤ ₚ) →
         (₁ + - a) * (a + - ₁) ≡ (a + - ₁) + (- (a * a) + a)
    vu a = begin
      (₁ + - a) * (a + - ₁)
        ≡⟨ *-distribʳ-+ (a + - ₁) ₁ (- a) ⟩
      ₁ * (a + - ₁) + (- a) * (a + - ₁)
        ≡⟨ Eq.cong₂ _+_ (*-identityˡ (a + - ₁)) (*-distribˡ-+ (- a) a (- ₁)) ⟩
      (a + - ₁) + ((- a) * a + (- a) * (- ₁))
        ≡⟨ Eq.cong ((a + - ₁) +_)
             (Eq.cong₂ _+_ (neg-* a a)
                (Eq.trans ([-x][-y]≈xy a ₁) (*-identityʳ a))) ⟩
      (a + - ₁) + (- (a * a) + a)
        ∎

  -- a + u + vu = -a² + 4a - 2.
  core : ∀ (a : ℤ ₚ) →
         (a + (a + - ₁)) + (₁ + - a) * (a + - ₁)
           ≡ - (a * a) + (₂ + ₂) * a + - ₂
  core a = begin
    (a + (a + - ₁)) + (₁ + - a) * (a + - ₁)
      ≡⟨ Eq.cong ((a + (a + - ₁)) +_) (vu a) ⟩
    (a + (a + - ₁)) + ((a + - ₁) + (- (a * a) + a))
      ≡⟨ shuffle ⟩
    (- (a * a) + ((a + a) + (a + a))) + (- ₁ + - ₁)
      ≡⟨ Eq.cong₂ _+_ (Eq.cong (- (a * a) +_) (Eq.sym (four-a a)))
                      (-‿+-comm ₁ ₁) ⟩
    - (a * a) + (₂ + ₂) * a + - ₂
      ∎
    where
    -- Four a's, two -1's and one -a², counted on each side.
    shuffle : (a + (a + - ₁)) + ((a + - ₁) + (- (a * a) + a))
                ≡ (- (a * a) + ((a + a) + (a + a))) + (- ₁ + - ₁)
    shuffle =
      CM.prove 3
        ((A CM.⊕ (A CM.⊕ N)) CM.⊕ ((A CM.⊕ N) CM.⊕ (Q CM.⊕ A)))
        ((Q CM.⊕ ((A CM.⊕ A) CM.⊕ (A CM.⊕ A))) CM.⊕ (N CM.⊕ N))
        (a ∷ - ₁ ∷ - (a * a) ∷ [])
      where
      A = CM.var ₀
      N = CM.var ₁
      Q = CM.var ₂

  -- The three cocycle terms, summed.
  phase : ∀ (a b k : ℤ ₚ) →
          (k * ((b * k) * (a * - k)) + k * (((a + - ₁) * k) * (b * - k)))
            + k * ((- ((₁ + - a) * k)) * (b * ((a + - ₁) * k)))
          ≡ - ((- (a * a) + (₂ + ₂) * a + - ₂) * (k * k * k) * b)
  phase a b k = begin
    (k * ((b * k) * (a * - k)) + k * ((u * k) * (b * - k)))
      + k * ((- (v * k)) * (b * (u * k)))
      ≡⟨ Eq.cong₂ _+_ (Eq.cong₂ _+_ t1 t2) t3 ⟩
    (- (K * (a * b)) + - (K * (u * b))) + - (K * ((v * u) * b))
      ≡⟨ Eq.cong (_+ - (K * ((v * u) * b)))
           (-‿+-comm (K * (a * b)) (K * (u * b))) ⟩
    - (K * (a * b) + K * (u * b)) + - (K * ((v * u) * b))
      ≡⟨ -‿+-comm (K * (a * b) + K * (u * b)) (K * ((v * u) * b)) ⟩
    - ((K * (a * b) + K * (u * b)) + K * ((v * u) * b))
      ≡⟨ Eq.cong -_ (r4 a u (v * u) b k) ⟩
    - (((a + u) + v * u) * K * b)
      ≡⟨ Eq.cong (λ t → - (t * K * b)) (core a) ⟩
    - ((- (a * a) + (₂ + ₂) * a + - ₂) * K * b)
      ∎
    where
    u = a + - ₁
    v = ₁ + - a
    K = k * k * k

    -- Pull the sign out of each term: σ = -k in the first two, -δ in
    -- the third.
    t1 : k * ((b * k) * (a * - k)) ≡ - (K * (a * b))
    t1 = begin
      k * ((b * k) * (a * - k))
        ≡⟨ Eq.cong (λ t → k * ((b * k) * t)) (*-neg a k) ⟩
      k * ((b * k) * - (a * k))
        ≡⟨ Eq.cong (k *_) (*-neg (b * k) (a * k)) ⟩
      k * - ((b * k) * (a * k))
        ≡⟨ *-neg k ((b * k) * (a * k)) ⟩
      - (k * ((b * k) * (a * k)))
        ≡⟨ Eq.cong -_ (r1 a b k) ⟩
      - (K * (a * b))
        ∎

    t2 : k * ((u * k) * (b * - k)) ≡ - (K * (u * b))
    t2 = begin
      k * ((u * k) * (b * - k))
        ≡⟨ Eq.cong (λ t → k * ((u * k) * t)) (*-neg b k) ⟩
      k * ((u * k) * - (b * k))
        ≡⟨ Eq.cong (k *_) (*-neg (u * k) (b * k)) ⟩
      k * - ((u * k) * (b * k))
        ≡⟨ *-neg k ((u * k) * (b * k)) ⟩
      - (k * ((u * k) * (b * k)))
        ≡⟨ Eq.cong -_ (r2 u b k) ⟩
      - (K * (u * b))
        ∎

    t3 : k * ((- (v * k)) * (b * (u * k))) ≡ - (K * ((v * u) * b))
    t3 = begin
      k * ((- (v * k)) * (b * (u * k)))
        ≡⟨ Eq.cong (k *_) (neg-* (v * k) (b * (u * k))) ⟩
      k * - ((v * k) * (b * (u * k)))
        ≡⟨ *-neg k ((v * k) * (b * (u * k))) ⟩
      - (k * ((v * k) * (b * (u * k))))
        ≡⟨ Eq.cong -_ (r3 v b u k) ⟩
      - (K * ((v * u) * b))
        ∎

------------------------------------------------------------------------
-- The calculus, at a fixed width

module Local (n : ℕ) where

  open SL.Local n
  open RL.Width (₁₊ n) using (Φ)

  ----------------------------------------------------------------------
  -- Two more left-multiplications
  --
  -- SemLocal has H· and S·; the multiplier also needs a whole S-power
  -- (a shear) and a whole Pauli (a translation) on the left.  Both are
  -- `has-•` with the left factor's shape fixed, then tidied.

  -- A shear: no X-part, the matrix (1 0 ; k 1), no phase.
  has-shear· : ∀ {u s k w x z a b c d φ} →
               Has u ₀ s ₁ ₀ k ₁ ₀ → Has w x z a b c d φ →
               Has (u • w) x (s + (k * x + z)) a b (k * a + c) (k * b + d)
                   (φ + h * (x * s))
  has-shear· {u} {s} {k} {w} {x} {z} {a} {b} {c} {d} {φ} hu hw =
    has-≡ (Eq.trans (+-identityˡ _) (oz x z))
          (Eq.cong (λ t → s + (k * x + t)) (*-identityˡ z))
          (oz a c) (oz b d)
          (Eq.cong (k * a +_) (*-identityˡ c))
          (Eq.cong (k * b +_) (*-identityˡ d))
          (Eq.cong₂ _+_ (+-identityˡ φ)
             (Eq.cong (h *_)
                (Eq.trans (Eq.cong₂ _+_ (negzero (k * x + ₁ * z))
                                        (Eq.cong (_* s) (oz x z)))
                          (+-identityˡ (x * s)))))
          (has-• hu hw)

  -- A translation: the Pauli (p , q), trivial action, no phase.
  has-trans· : ∀ {u p q w x z a b c d φ} →
               Has u p q ₁ ₀ ₀ ₁ ₀ → Has w x z a b c d φ →
               Has (u • w) (p + x) (q + z) a b c d
                   (φ + h * ((- p) * z + x * q))
  has-trans· {u} {p} {q} {w} {x} {z} {a} {b} {c} {d} {φ} hu hw =
    has-≡ (Eq.cong (p +_) (oz x z)) (Eq.cong (q +_) (zo x z))
          (oz a c) (oz b d) (zo a c) (zo b d)
          (Eq.cong₂ _+_ (+-identityˡ φ)
             (Eq.cong (h *_)
                (Eq.cong₂ _+_ (Eq.cong ((- p) *_) (zo x z))
                              (Eq.cong (_* q) (oz x z)))))
          (has-• hu hw)

  -- S to a power in ℤ/pℤ, with its exponent read back.
  has-S^' : ∀ (y : ℤ ₚ) → Has (S^ {n} y) ₀ (y * σ) ₁ ₀ y ₁ ₀
  has-S^' y =
    has-≡ Eq.refl (Eq.cong (_* σ) (mult-toℕ y)) Eq.refl Eq.refl
          (mult-toℕ y) Eq.refl Eq.refl (has-S^ (toℕ y))

  ----------------------------------------------------------------------
  -- X, and its powers
  --
  -- X = H S H H S⁻¹ H is the Pauli (1 , 0), acts trivially and carries
  -- no phase — Z's partner (SemLocal.has-Z), by the same chain read from
  -- the right.  σ + σ = -1 is the only fact about ½ it uses.

  private
    x2 : Has (S⁻¹ • H {n}) ₀ (- σ) ₀ (- ₁) ₁ ₁ ₀
    x2 = has-≡ Eq.refl
               (Eq.trans (Eq.cong (- σ +_)
                            (Eq.trans (+-identityʳ ((- ₁) * ₀))
                                      (*-zeroʳ (- ₁))))
                         (+-identityʳ (- σ)))
               Eq.refl Eq.refl
               (Eq.trans (Eq.cong (_+ ₁) (*-zeroʳ (- ₁))) (+-identityˡ ₁))
               (Eq.trans (+-identityʳ ((- ₁) * (- ₁))) mm)
               (0h0 (- σ))
               (has-shear· has-S⁻¹ has-H)

    x3 : Has (H • S⁻¹ • H {n}) σ ₀ (- ₁) (- ₁) ₀ (- ₁) ₀
    x3 = has-≡ (-‿involutive σ) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
               Eq.refl (has-H· x2)

    x4 : Has (H • H • S⁻¹ • H {n}) ₀ σ ₀ ₁ (- ₁) (- ₁) ₀
    x4 = has-≡ -0#≈0# Eq.refl -0#≈0# (-‿involutive ₁) Eq.refl Eq.refl
               Eq.refl (has-H· x3)

    x5 : Has (S • H • H • S⁻¹ • H {n}) ₀ (- ₁) ₀ ₁ (- ₁) ₀ ₀
    x5 = has-≡ Eq.refl
               (Eq.trans (Eq.cong (σ +_) (+-identityˡ σ)) σ+σ)
               Eq.refl Eq.refl (+-identityˡ (- ₁)) (+-inverseʳ ₁)
               (Eq.trans (Eq.cong (₀ +_) (h0 σ)) (+-identityˡ ₀))
               (has-S· x4)

  has-X : Has (X {n}) ₁ ₀ ₁ ₀ ₀ ₁ ₀
  has-X = has-≡ (-‿involutive ₁) Eq.refl (-‿involutive ₁) -0#≈0#
                Eq.refl Eq.refl Eq.refl (has-H· x5)

  has-X^ : ∀ k → Has (X {n} ^ k) (mult k) ₀ ₁ ₀ ₀ ₁ ₀
  has-X^ zero      = has-ε
  has-X^ (₁₊ zero) =
    has-≡ (Eq.sym (+-identityʳ ₁)) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
          Eq.refl has-X
  has-X^ (₂₊ k) =
    has-≡ Eq.refl (+-identityˡ ₀) Eq.refl Eq.refl Eq.refl Eq.refl
          (Eq.trans (+-identityˡ _)
             (Eq.trans (Eq.cong (h *_)
                          (Eq.trans (Eq.cong₂ _+_ (*-zeroʳ (- ₁))
                                                  (*-zeroʳ (mult (₁₊ k))))
                                    (+-identityˡ ₀)))
                       (*-zeroʳ h)))
          (has-trans· has-X (has-X^ (₁₊ k)))

  has-X^' : ∀ (y : ℤ ₚ) → Has (X^ y {n}) y ₀ ₁ ₀ ₀ ₁ ₀
  has-X^' y =
    has-≡ (mult-toℕ y) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
          (has-X^ (toℕ y))

  ----------------------------------------------------------------------
  -- The multiplier word, for any a, b with ab = 1
  --
  -- SHS' a b read from the right, one step per letter block.  The Pauli
  -- is kept in the form (coefficient)·½ throughout, which is what makes
  -- X^δ and Z^γ cancel it in one `cancel-pair*` each.

  module Block (a b : ℤ ₚ) (ab : a * b ≡ ₁) where

    private
      ba : b * a ≡ ₁
      ba = Eq.trans (*-comm b a) ab

      u : ℤ ₚ
      u = a + - ₁

      -- The phase after S^a, and after the second S^b.
      φ₄ φ₆ : ℤ ₚ
      φ₄ = h * ((b * h) * (a * σ))
      φ₆ = φ₄ + h * ((u * h) * (b * σ))

      c2 : Has (S^ b • H {n}) ₀ (b * σ) ₀ (- ₁) ₁ (- b) ₀
      c2 = has-≡ Eq.refl
                 (Eq.trans (Eq.cong (b * σ +_)
                              (Eq.trans (+-identityʳ (b * ₀)) (*-zeroʳ b)))
                           (+-identityʳ (b * σ)))
                 Eq.refl Eq.refl
                 (Eq.trans (Eq.cong (_+ ₁) (*-zeroʳ b)) (+-identityˡ ₁))
                 (Eq.trans (+-identityʳ (b * (- ₁))) (*-neg₁ b))
                 (0h0 (b * σ))
                 (has-shear· (has-S^' b) has-H)

      c3 : Has (H • S^ b • H {n}) (b * h) ₀ (- ₁) b ₀ (- ₁) ₀
      c3 = has-≡ (Eq.trans (-‿distribʳ-* b (- h))
                           (Eq.cong (b *_) (-‿involutive h)))
                 Eq.refl Eq.refl (-‿involutive b) Eq.refl Eq.refl Eq.refl
                 (has-H· c2)

      c4 : Has (S^ a • H • S^ b • H {n})
               (b * h) ((₁ + - a) * h) (- ₁) b (- a) ₀ φ₄
      c4 = has-≡ Eq.refl z4
                 Eq.refl Eq.refl
                 (Eq.trans (+-identityʳ (a * (- ₁))) (*-neg₁ a))
                 (Eq.trans (Eq.cong (_+ - ₁) ab) (+-inverseʳ ₁))
                 (+-identityˡ φ₄)
                 (has-shear· (has-S^' a) c3)
        where
        z4 : a * σ + (a * (b * h) + ₀) ≡ (₁ + - a) * h
        z4 = begin
          a * σ + (a * (b * h) + ₀)
            ≡⟨ Eq.cong (a * σ +_)
                 (Eq.trans (+-identityʳ (a * (b * h)))
                   (Eq.trans (Eq.sym (*-assoc a b h))
                     (Eq.trans (Eq.cong (_* h) ab) (*-identityˡ h)))) ⟩
          a * σ + h
            ≡⟨ Eq.cong (_+ h) (Eq.trans (*-neg a h) (Eq.sym (neg-* a h))) ⟩
          (- a) * h + h
            ≡⟨ +-comm ((- a) * h) h ⟩
          h + (- a) * h
            ≡⟨ Eq.cong (_+ (- a) * h) (Eq.sym (*-identityˡ h)) ⟩
          ₁ * h + (- a) * h
            ≡⟨ Eq.sym (*-distribʳ-+ h ₁ (- a)) ⟩
          (₁ + - a) * h
            ∎

      c5 : Has (H • S^ a • H • S^ b • H {n})
               (u * h) (b * h) a ₀ (- ₁) b φ₄
      c5 = has-≡ x5' Eq.refl (-‿involutive a) -0#≈0# Eq.refl Eq.refl
                 Eq.refl (has-H· c4)
        where
        x5' : - ((₁ + - a) * h) ≡ u * h
        x5' = begin
          - ((₁ + - a) * h)
            ≡⟨ -‿distribˡ-* (₁ + - a) h ⟩
          (- (₁ + - a)) * h
            ≡⟨ Eq.cong (_* h) (Eq.sym (-‿+-comm ₁ (- a))) ⟩
          (- ₁ + - (- a)) * h
            ≡⟨ Eq.cong (λ t → (- ₁ + t) * h) (-‿involutive a) ⟩
          (- ₁ + a) * h
            ≡⟨ Eq.cong (_* h) (+-comm (- ₁) a) ⟩
          u * h
            ∎

      c6 : Has (S^ b • H • S^ a • H • S^ b • H {n})
               (u * h) (b * (u * h)) a ₀ ₀ b φ₆
      c6 = has-≡ Eq.refl z6 Eq.refl Eq.refl
                 (Eq.trans (Eq.cong (_+ - ₁) ba) (+-inverseʳ ₁))
                 (Eq.trans (Eq.cong (_+ b) (*-zeroʳ b)) (+-identityˡ b))
                 Eq.refl
                 (has-shear· (has-S^' b) c5)
        where
        -- σ + (y + h) = y, as σ = -h.
        σ+[y+h] : ∀ (y : ℤ ₚ) → σ + (y + h) ≡ y
        σ+[y+h] y = begin
          σ + (y + h)     ≡⟨ Eq.cong (σ +_) (+-comm y h) ⟩
          - h + (h + y)   ≡⟨ Eq.sym (+-assoc (- h) h y) ⟩
          (- h + h) + y   ≡⟨ Eq.cong (_+ y) (+-inverseˡ h) ⟩
          ₀ + y           ≡⟨ +-identityˡ y ⟩
          y               ∎

        z6 : b * σ + (b * (u * h) + b * h) ≡ b * (u * h)
        z6 = begin
          b * σ + (b * (u * h) + b * h)
            ≡⟨ Eq.cong (b * σ +_) (Eq.sym (*-distribˡ-+ b (u * h) h)) ⟩
          b * σ + b * (u * h + h)
            ≡⟨ Eq.sym (*-distribˡ-+ b σ (u * h + h)) ⟩
          b * (σ + (u * h + h))
            ≡⟨ Eq.cong (b *_) (σ+[y+h] (u * h)) ⟩
          b * (u * h)
            ∎

      -- X^δ cancels the X-part ...
      c7 : Has (X^ ((₁ + - a) * 1/2) • S^ b • H • S^ a • H • S^ b • H {n})
               ₀ (b * (u * h)) a ₀ ₀ b
               (φ₆ + h * ((- ((₁ + - a) * h)) * (b * (u * h))))
      c7 = has-≡ (cancel-pair* ₁ a h) (+-identityˡ (b * (u * h)))
                 Eq.refl Eq.refl Eq.refl Eq.refl
                 (Eq.cong (λ t → φ₆ + h * t)
                    (Eq.trans
                       (Eq.cong ((- ((₁ + - a) * h)) * (b * (u * h)) +_)
                                (*-zeroʳ (u * h)))
                       (+-identityʳ _)))
                 (has-trans· (has-X^' ((₁ + - a) * 1/2)) c6)

    -- ... and Z^γ the Z-part, leaving the pure multiplier.
    has-SHS' : Has (SHS' {n} a b) ₀ ₀ a ₀ ₀ b
                   (- ((- (a * a) + (₂ + ₂) * a + - ₂) * F.1/8 * b))
    has-SHS' =
      has-≡ (+-identityˡ ₀) z8 Eq.refl Eq.refl Eq.refl Eq.refl
            (Eq.trans
               (Eq.cong (φ₇ +_)
                  (Eq.trans (Eq.cong (h *_)
                               (Eq.trans (Eq.cong₂ _+_
                                            (negzero (b * (u * h)))
                                            (*-zeroˡ ((b + - ₁) * 1/2)))
                                         (+-identityˡ ₀)))
                            (*-zeroʳ h)))
               (Eq.trans (+-identityʳ φ₇) (Arith.phase a b h)))
            (has-trans· (has-Z^' ((b + - ₁) * 1/2)) c7)
      where
      φ₇ : ℤ ₚ
      φ₇ = φ₆ + h * ((- ((₁ + - a) * h)) * (b * (u * h)))

      -- b(a - 1) = 1 - b, so the Z-parts cancel.
      z8 : (b + - ₁) * 1/2 + b * (u * h) ≡ ₀
      z8 = begin
        (b + - ₁) * h + b * (u * h)
          ≡⟨ Eq.cong ((b + - ₁) * h +_) (Eq.sym (*-assoc b u h)) ⟩
        (b + - ₁) * h + (b * u) * h
          ≡⟨ Eq.cong (λ t → (b + - ₁) * h + t * h) bu ⟩
        (b + - ₁) * h + (₁ + - b) * h
          ≡⟨ cancel-pair* b ₁ h ⟩
        ₀
          ∎
        where
        bu : b * u ≡ ₁ + - b
        bu = Eq.trans (*-distribˡ-+ b a (- ₁))
                      (Eq.cong₂ _+_ ba (*-neg₁ b))

  open Block public using (has-SHS')

  ----------------------------------------------------------------------
  -- XM, Figure 1's multiplier without its scalars

  has-XM : ∀ (x : ℤ* ₚ) →
           Has (XM {n} x) ₀ ₀ (x .proj₁) ₀ ₀ ((x ⁻¹) .proj₁) (- F.M-phase x)
  has-XM x = has-SHS' (x .proj₁) ((x ⁻¹) .proj₁)
                      (lemma-⁻¹ʳ (x .proj₁)
                         {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂}}})

  Φ-XM : ∀ (x : ℤ* ₚ) → Φ (XM {n} x) ≡ - F.M-phase x
  Φ-XM x = Has.phase (has-XM x)

  ----------------------------------------------------------------------
  -- Pauli-free words with a phase
  --
  -- SemLocal's `Free` with the phase left free: with no Pauli on either
  -- side the cocycle vanishes, so phases add under products and
  -- multiply under powers.

  Phased : QS.Circuit (₁₊ n) → ℤ ₚ → Set
  Phased w φ = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → Has w ₀ ₀ a b c d φ

  phased-Φ : ∀ {w φ} → Phased w φ → Φ w ≡ φ
  phased-Φ (_ , _ , _ , _ , hw) = Has.phase hw

  phased-≡ : ∀ {w φ φ'} → φ ≡ φ' → Phased w φ → Phased w φ'
  phased-≡ e (a , b , c , d , hw) =
    a , b , c , d ,
    has-≡ Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl e hw

  phased-• : ∀ {u v φ ψ} → Phased u φ → Phased v ψ → Phased (u • v) (φ + ψ)
  phased-• {u} {v} {φ} {ψ} (a , b , c , d , hu) (a' , b' , c' , d' , hv) =
    _ , _ , _ , _ ,
    has-≡ (Eq.trans (+-identityˡ _)
             (Eq.trans (Eq.cong₂ _+_ (*-zeroʳ a) (*-zeroʳ b))
                       (+-identityʳ ₀)))
          (Eq.trans (+-identityˡ _)
             (Eq.trans (Eq.cong₂ _+_ (*-zeroʳ c) (*-zeroʳ d))
                       (+-identityʳ ₀)))
          Eq.refl Eq.refl Eq.refl Eq.refl
          (Eq.trans (Eq.cong ((φ + ψ) +_)
                       (Eq.trans (Eq.cong (h *_)
                                    (Eq.trans (Eq.cong₂ _+_
                                                 (negzero (c * ₀ + d * ₀))
                                                 (*-zeroʳ (a * ₀ + b * ₀)))
                                              (+-identityʳ ₀)))
                                 (*-zeroʳ h)))
                    (+-identityʳ (φ + ψ)))
          (has-• hu hv)

  phased-^ : ∀ {w φ} → Phased w φ → ∀ k → Phased (w ^ k) (mult k * φ)
  phased-^ {w} {φ} pw zero =
    phased-≡ (Eq.sym (*-zeroˡ φ)) (₁ , ₀ , ₀ , ₁ , has-ε)
  phased-^ {w} {φ} pw (₁₊ zero) =
    phased-≡ (Eq.sym (Eq.trans (Eq.cong (_* φ) (+-identityʳ ₁))
                               (*-identityˡ φ)))
             pw
  phased-^ {w} {φ} pw (₂₊ k) =
    phased-≡ (Eq.sym (Eq.trans (*-distribʳ-+ φ ₁ (mult (₁₊ k)))
                               (Eq.cong (_+ mult (₁₊ k) * φ) (*-identityˡ φ))))
             (phased-• pw (phased-^ pw (₁₊ k)))

  phased-XM : ∀ (x : ℤ* ₚ) → Phased (XM {n} x) (- F.M-phase x)
  phased-XM x = _ , _ , _ , _ , has-XM x

  Φ-XM^ : ∀ (x : ℤ* ₚ) (k : ℕ) → Φ (XM {n} x ^ k) ≡ mult k * (- F.M-phase x)
  Φ-XM^ x k = phased-Φ (phased-^ (phased-XM x) k)

  -- ... at the primitive root, with the exponent in ℤ/pℤ (M-power's
  -- left-hand side).
  Φ-XMg^ : ∀ (k : ℤ ₚ) → Φ (XMg^ k {n}) ≡ k * (- F.M-phase g′)
  Φ-XMg^ k =
    Eq.trans (Φ-XM^ g′ (toℕ k)) (Eq.cong (_* (- F.M-phase g′)) (mult-toℕ k))

  ----------------------------------------------------------------------
  -- Figure 1's C4
  --
  -- semi-MS : XMg • S === Z^c • S^d • XMg.  The cocycle pairs X-parts
  -- with Z-parts, and no cocycle term survives on either side: on the
  -- left S meets XMg's trivial Pauli, on the right Z^c, S^d and XMg have
  -- no X-part between them.  So both sides carry XMg's phase, whatever
  -- c and d are.

  Φ-semi-MS' : ∀ (c d : ℤ ₚ) →
               Φ (XMg {n} • S) ≡ Φ (Z^ c • S^ d • XMg {n})
  Φ-semi-MS' c d = Eq.trans lhs (Eq.sym rhs)
    where
    φg : ℤ ₚ
    φg = - F.M-phase g′

    hg = has-XM g′

    lhs : Φ (XMg {n} • S) ≡ φg
    lhs = begin
      Φ (XMg • S)
        ≡⟨ Has.phase (has-• hg has-S) ⟩
      (φg + ₀) + h * ((- ₀) * (₀ * ₀ + g⁻¹ * σ) + (g * ₀ + ₀ * σ) * ₀)
        ≡⟨ Eq.cong ((φg + ₀) +_)
             (Eq.trans (Eq.cong (h *_)
                          (Eq.trans (Eq.cong₂ _+_
                                       (negzero (₀ * ₀ + g⁻¹ * σ))
                                       (*-zeroʳ (g * ₀ + ₀ * σ)))
                                    (+-identityʳ ₀)))
                       (*-zeroʳ h)) ⟩
      (φg + ₀) + ₀
        ≡⟨ Eq.trans (+-identityʳ (φg + ₀)) (+-identityʳ φg) ⟩
      φg
        ∎

    -- S^d • XMg, with its phase tidied.
    r : Has (S^ d • XMg {n}) ₀ (d * σ + (d * ₀ + ₀)) g ₀ (d * g + ₀)
            (d * ₀ + g⁻¹) φg
    r = has-≡ Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
              (Eq.trans (Eq.cong (φg +_) (h0 (d * σ))) (+-identityʳ φg))
              (has-shear· (has-S^' d) hg)

    rhs : Φ (Z^ c • S^ d • XMg {n}) ≡ φg
    rhs = begin
      Φ (Z^ c • S^ d • XMg)
        ≡⟨ Has.phase (has-trans· (has-Z^' c) r) ⟩
      φg + h * ((- ₀) * (d * σ + (d * ₀ + ₀)) + ₀ * c)
        ≡⟨ Eq.cong (φg +_)
             (Eq.trans (Eq.cong (h *_)
                          (Eq.trans (Eq.cong₂ _+_
                                       (negzero (d * σ + (d * ₀ + ₀)))
                                       (*-zeroˡ c))
                                    (+-identityʳ ₀)))
                       (*-zeroʳ h)) ⟩
      φg + ₀
        ≡⟨ +-identityʳ φg ⟩
      φg
        ∎

  -- Exactly the two sides of FQ's semi-MS, whose exponents are SemiMS's
  -- c and d by definition.
  Φ-semi-MS : Φ (XMg {n} • S)
              ≡ Φ (Z^ ((₁ + - g) * 1/2 * (g⁻¹ * g⁻¹))
                   • S^ (g⁻¹ * g⁻¹) • XMg {n})
  Φ-semi-MS = Φ-semi-MS' SMS.c SMS.d

  ----------------------------------------------------------------------
  -- H², which order-H equates with XM₋₁

  Φ-H² : Φ (H {n} ^ 2) ≡ ₀
  Φ-H² = free-Φ (free-^ free-H 2)
