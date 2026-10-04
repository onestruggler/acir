------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure1-MS variant: C4 is Paper-V1 semi-MR with its sides swapped.
-- All other Figure 1 axioms and scalar conventions are unchanged.
--
-- Every rule of Figure 1 holds in the rule set with -1.
--
-- Translation's `new` reads a Figure-1 word in the rule set with -1:
-- ν = -ω becomes -1 • ω and the gates stay gates.  This module shows
-- that it respects each of Figure 1's relations C0–C15 and the
-- structural rules, i.e. that `new` is well defined on Figure 1.
--
-- Images.agda puts the image of each rule's two sides in the form
--
--     ⌜ u ⌝ • (a scalar),
--
-- u a circuit of Paper-V0's gates.  What is left is then always the
-- same two-part argument:
--
--   * the gate parts.  Mod scalars, u ≈ v is a theorem of Paper-V0
--     (most rules are Paper-V0 rules verbatim; C2, C3, C4, C9 are
--     Figure 1 mod scalars' rules, which Figure1.ModScalar.Iso carries
--     into Paper-V0).  ExactLift turns that into an exact equation
--     ⌜ u ⌝ ≈ ω^c • ⌜ v ⌝, where c = Φ u - Φ v is the phase difference
--     the exact group assigns — which SemFigure1 computes;
--   * the scalars.  Collected on the right, they must agree, and do:
--     the powers of -1 by Legendre's sign arithmetic, the powers of ω
--     by an equation in ℤₚ.
--
-- The phases are where Figure 1's scalars come from.  The S-spelled
-- multiplier word XM a has phase (a² - 4a + 2)/(8a) in the exact group
-- (SemFigure1.Φ-XM), and T1 multiplies it by exactly ω to minus that:
-- the reason M_a maps |x⟩ to |ax⟩ on the nose.  Everything else on one
-- wire is phase-free, and on two and three wires the scalars that occur
-- are the λ_p² of the swap, which pair off.
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

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.Derived
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

import Data.Nat as Nat
open import Data.Product using (proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (tt)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ)
open import Presentation.Construct.Properties.Extension using (tw)

open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
  using (mult ; mult-toℕ)

open Primitive-Root-Modp' g* g-gen using (g′ ; g^_)

import Examples.Groups.Clifford+MinusOne.Qupit.Syntactics
  p-3 p-prime g* g-gen as N
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.Syntactics
  p-3 p-prime g* g-gen as F
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.ModScalar.Syntactics
  p-3 p-prime g* g-gen as FQ
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.ModScalar.Iso
  p-3 p-prime g* g-gen as FQIso
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.ModScalar.SemiMS
  p-3 p-prime g* g-gen as SMS
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.Translation
  p-3 p-prime g* g-gen as T
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.Images
  p-3 p-prime g* g-gen as Im
import Examples.Groups.Clifford+MinusOne.Qupit.ExactLift
  p-3 p-prime g* g-gen as XL
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.SemFigure1
  p-3 p-prime g* g-gen as SF
import Examples.Groups.Clifford.Qupit.SemRealises
  p-3 p-prime g* g-gen as RL

open T using (Alph ; _≈±_ ; Gʷ ; ⇑ ; new)
open FQ using (Gen ; SympGate ; H-gate ; S-gate ; CZ-gate
              ; S ; H ; CZ ; S^ ; CZ^ ; Ex ; CX ; CZ02 ; _↑ ; _↓)
module FQR = FQ.Clifford-Relations
module V0R = N.CR

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Two ways into the exact layer

-- A Paper-V0 relator whose correction is trivial — all but order-SH.
twist0 : ∀ {u v} (r : n V0R.QRel, u === v) → N.corr r ≡ ε →
         N.⌜ u ⌝ ≈± N.⌜ v ⌝
twist0 {n} {u} {v} r e =
  PB.trans (PB.axiom (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.right (tw r)))))
    (Eq.subst (λ c → [ [ c ]ₗ • [ v ]ᵣ ]ₗ ≈± N.⌜ v ⌝) (Eq.sym e)
              PB.left-unit)

-- A Paper-V0 derivation between two words of the same phase.
lift0 : ∀ n {a b : Word (Gen n)} → PB._≈_ (n V0R.QRel,_===_) a b →
        RL.Width.Φ n a ≡ RL.Width.Φ n b → N.⌜ a ⌝ ≈± N.⌜ b ⌝
lift0 n d e =
  PB.trans (XL.exact-lift± n d ₀ (Eq.trans e (Eq.sym (+-identityˡ _))))
           PB.left-unit

-- Figure 1 mod scalars, read in Paper-V0.
fq : ∀ {u v : Word (Gen n)} → n FQR.QRel, u === v →
     PB._≈_ (n V0R.QRel,_===_) u v
fq {n} r = FQIso.Theorem.fq⇒v0 n (PB.axiom r)

------------------------------------------------------------------------
-- Two identities in ℤₚ

-- (a + b) + - b = a.
cancelʳ : ∀ (a b : ℤ ₚ) → (a + b) + - b ≡ a
cancelʳ a b = Eq.trans (+-assoc a b (- b))
                (Eq.trans (Eq.cong (a +_) (+-inverseʳ b)) (+-identityʳ a))

-- ((-t)·k + s) + t·k = s.
sum-k : ∀ (t k s : ℤ ₚ) → ((- t) * k + s) + t * k ≡ s
sum-k t k s = begin
  ((- t) * k + s) + t * k   ≡⟨ +-assoc ((- t) * k) s (t * k) ⟩
  (- t) * k + (s + t * k)   ≡⟨ Eq.cong ((- t) * k +_) (+-comm s (t * k)) ⟩
  (- t) * k + (t * k + s)   ≡⟨ Eq.sym (+-assoc ((- t) * k) (t * k) s) ⟩
  ((- t) * k + t * k) + s
    ≡⟨ Eq.cong (_+ s) (Eq.sym (*-distribʳ-+ k (- t) t)) ⟩
  ((- t) + t) * k + s       ≡⟨ Eq.cong (λ z → z * k + s) (+-inverseˡ t) ⟩
  ₀ * k + s                 ≡⟨ Eq.cong (_+ s) (*-zeroˡ k) ⟩
  ₀ + s                     ≡⟨ +-identityˡ s ⟩
  s                         ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Single qudit

module One (n : ℕ) where

  open T.Algebra (₁₊ n)
  open Im.Scalars (₁₊ n)
  open Im.Multiplier n
  open SR word-setoid
  module Φ = RL.Width (₁₊ n)
  module SFL = SF.Local n

  -- C1.
  c1 : Gʷ (F.S {n} ^ p) ≈ ε
  c1 = trans (refl' (Im.G-pow F.S S Eq.refl p))
             (twist0 V0R.order-S Eq.refl)

  -- C2: H² = M₋₁ · (-1)^((p-1)/2).  The phase of M₋₁'s word is minus
  -- T1's exponent, and the two signs (-1/p) and (-1)^((p-1)/2) cancel.
  c2 : Gʷ (F.H {n} ^ 2) ≈ Gʷ (F.M₋₁ • F.λ²)
  c2 = begin
    N.⌜ H ^ 2 ⌝
      ≈⟨ XL.exact-lift± (₁₊ n) (fq FQR.order-H) t phase ⟩
    ωℤ t • N.⌜ FQR.XM x ⌝
      ≈⟨ sym (ω^-central (toℕ t) _) ⟩
    N.⌜ FQR.XM x ⌝ • ωℤ t
      ≈⟨ cright sym left-unit ⟩
    N.⌜ FQR.XM x ⌝ • (ε • ωℤ t)
      ≈⟨ cright cleft sym (Sg.sign-₋₁) ⟩
    N.⌜ FQR.XM x ⌝ • ((Sg.sign x • N.-1± ^ F.p-1/2) • ωℤ t)
      ≈⟨ cright scal ⟩
    N.⌜ FQR.XM x ⌝ • (M-scalar x • N.-1± ^ F.p-1/2)
      ≈⟨ sym assoc ⟩
    (N.⌜ FQR.XM x ⌝ • M-scalar x) • N.-1± ^ F.p-1/2
      ≈⟨ sym (cong (G-M x) G-λ²) ⟩
    Gʷ (F.M₋₁ • F.λ²)
      ∎
    where
    x = -'₁
    t = F.M-phase x

    phase : Φ.Φ (H ^ 2) ≡ t + Φ.Φ (FQR.XM x)
    phase = Eq.trans SFL.Φ-H²
              (Eq.sym (Eq.trans (Eq.cong (t +_) (SFL.Φ-XM x))
                                (+-inverseʳ t)))

    -- (s • m) • w ≈ (s • w) • m, w = ωℤ t central.
    scal : (Sg.sign x • N.-1± ^ F.p-1/2) • ωℤ t
           ≈ (Sg.sign x • ωℤ t) • N.-1± ^ F.p-1/2
    scal = begin
      (Sg.sign x • N.-1± ^ F.p-1/2) • ωℤ t   ≈⟨ assoc ⟩
      Sg.sign x • (N.-1± ^ F.p-1/2 • ωℤ t)   ≈⟨ cright ω^-central (toℕ t) _ ⟩
      Sg.sign x • (ωℤ t • N.-1± ^ F.p-1/2)   ≈⟨ sym assoc ⟩
      (Sg.sign x • ωℤ t) • N.-1± ^ F.p-1/2   ∎

  -- C3: (M_g)^k = M_(g^k).  The phases add up, since the multiplier
  -- word is Pauli-free, and the signs multiply, by Euler's criterion.
  c3 : ∀ (k : ℤ ₚ) → Gʷ (F.Mg {n} ^ toℕ k) ≈ Gʷ (F.M (g^ k))
  c3 k = begin
    Gʷ (F.Mg ^ K)
      ≡⟨ Im.G^ F.Mg K ⟩
    Gʷ F.Mg ^ K
      ≈⟨ ^-cong _ _ K (G-M g′) ⟩
    (N.⌜ FQR.XMg ⌝ • M-scalar g′) ^ K
      ≈⟨ ^-• _ _ K (central-M-scalar g′ _) ⟩
    N.⌜ FQR.XMg ⌝ ^ K • M-scalar g′ ^ K
      ≡⟨ Eq.cong (_• M-scalar g′ ^ K) (Eq.sym (Im.⌜^⌝ FQR.XMg K)) ⟩
    N.⌜ FQR.XMg ^ K ⌝ • M-scalar g′ ^ K
      ≈⟨ cong (XL.exact-lift± (₁₊ n) (fq (FQR.M-power k)) c phase) scals ⟩
    (ωℤ c • N.⌜ FQR.XM (g^ k) ⌝) • (Sg.sign (g^ k) • ωℤ (tg * k))
      ≈⟨ cleft sym (ω^-central (toℕ c) _) ⟩
    (N.⌜ FQR.XM (g^ k) ⌝ • ωℤ c) • (Sg.sign (g^ k) • ωℤ (tg * k))
      ≈⟨ assoc ⟩
    N.⌜ FQR.XM (g^ k) ⌝ • (ωℤ c • (Sg.sign (g^ k) • ωℤ (tg * k)))
      ≈⟨ cright gather ⟩
    N.⌜ FQR.XM (g^ k) ⌝ • (Sg.sign (g^ k) • ωℤ tk)
      ≈⟨ sym (G-M (g^ k)) ⟩
    Gʷ (F.M (g^ k))
      ∎
    where
    K = toℕ k
    tg = F.M-phase g′
    tk = F.M-phase (g^ k)
    c = (- tg) * k + tk

    -- Φ (XM g ^ k) = k · (-tg), against Φ (XM (g^k)) = -tk.
    phase : Φ.Φ (FQR.XMg ^ K) ≡ c + Φ.Φ (FQR.XM (g^ k))
    phase =
      Eq.trans (SFL.Φ-XM^ g′ K)
        (Eq.trans (Eq.cong (_* (- tg)) (mult-toℕ k))
          (Eq.trans (*-comm k (- tg))
            (Eq.trans (Eq.sym (cancelʳ ((- tg) * k) tk))
              (Eq.cong (c +_) (Eq.sym (SFL.Φ-XM (g^ k)))))))

    scals : M-scalar g′ ^ K ≈ Sg.sign (g^ k) • ωℤ (tg * k)
    scals = begin
      (Sg.sign g′ • ωℤ tg) ^ K
        ≈⟨ ^-• _ _ K (sym (central-sign g′ _)) ⟩
      Sg.sign g′ ^ K • ωℤ tg ^ K
        ≈⟨ cong (sym (Sg.sign-g^ k)) (ωℤ-* tg k) ⟩
      Sg.sign (g^ k) • ωℤ (tg * k)
        ∎

    gather : ωℤ c • (Sg.sign (g^ k) • ωℤ (tg * k))
             ≈ Sg.sign (g^ k) • ωℤ tk
    gather = begin
      ωℤ c • (Sg.sign (g^ k) • ωℤ (tg * k))   ≈⟨ sym assoc ⟩
      (ωℤ c • Sg.sign (g^ k)) • ωℤ (tg * k)
        ≈⟨ cleft sym (ω^-central (toℕ c) _) ⟩
      (Sg.sign (g^ k) • ωℤ c) • ωℤ (tg * k)   ≈⟨ assoc ⟩
      Sg.sign (g^ k) • (ωℤ c • ωℤ (tg * k))   ≈⟨ cright ωℤ-+ c (tg * k) ⟩
      Sg.sign (g^ k) • ωℤ (c + tg * k)
        ≈⟨ cright ωℤ-cong (sum-k tg k tk) ⟩
      Sg.sign (g^ k) • ωℤ tk                  ∎

  -- C4: S M_g = M_g S^(g²) Z^((g²-g)/2).
  c4 : Gʷ (F.S {n} • F.Mg)
       ≈ Gʷ (F.Mg • F.S^ (g * g) • F.Z^ SMS.e)
  c4 = begin
    N.⌜ S ⌝ • Gʷ F.Mg
      ≈⟨ cright G-M g′ ⟩
    N.⌜ S ⌝ • (N.⌜ FQR.XMg ⌝ • s)
      ≈⟨ sym assoc ⟩
    N.⌜ S • FQR.XMg ⌝ • s
      ≈⟨ cleft lift0 (₁₊ n) (fq FQR.semi-MS) SFL.Φ-semi-MS ⟩
    N.⌜ FQR.XMg • S^ a • FQR.Z^ SMS.e ⌝ • s
      ≈⟨ assoc ⟩
    N.⌜ FQR.XMg ⌝ • (N.⌜ S^ a • FQR.Z^ SMS.e ⌝ • s)
      ≈⟨ cright central-M-scalar g′ _ ⟩
    N.⌜ FQR.XMg ⌝ • (s • N.⌜ S^ a • FQR.Z^ SMS.e ⌝)
      ≈⟨ sym assoc ⟩
    (N.⌜ FQR.XMg ⌝ • s) • N.⌜ S^ a • FQR.Z^ SMS.e ⌝
      ≈⟨ sym (cong (G-M g′)
              (cong (refl' (Im.G-S^ a)) (refl' (Im.G-Z^ SMS.e)))) ⟩
    Gʷ (F.Mg • F.S^ a • F.Z^ SMS.e)
      ∎
    where
    s = M-scalar g′
    a = g * g

  -- C5.
  c5 : Gʷ (F.S {n} • F.H • F.H • F.S • F.H • F.H)
       ≈ Gʷ (F.H • F.H • F.S • F.H • F.H • F.S)
  c5 = sym (twist0 V0R.comm-HHSHHS Eq.refl)

------------------------------------------------------------------------
-- The scalar

-- C0: (-ω)^(2p) = 1.
c0 : Gʷ (F.ν {n} ^ (p Nat.+ p)) ≈± ε
c0 {n} = begin
  Gʷ (F.ν ^ (p Nat.+ p))               ≡⟨ Im.G^ F.ν (p Nat.+ p) ⟩
  N.-ω± ^ (p Nat.+ p)                  ≈⟨ ^-+ N.-ω± p p ⟩
  N.-ω± ^ p • N.-ω± ^ p
    ≡⟨ Eq.sym (Eq.cong₂ _•_ (Im.G^ F.ν p) (Im.G^ F.ν p)) ⟩
  Gʷ F.-1ˢ • Gʷ F.-1ˢ                  ≈⟨ cong G--1 G--1 ⟩
  N.-1± • N.-1±                        ≈⟨ -1²≈ε ⟩
  ε                                    ∎
  where
  open T.Algebra n
  open Im.Scalars n
  open SR word-setoid

------------------------------------------------------------------------
-- Two qudits

module Two (n : ℕ) where

  open T.Algebra (₂₊ n)
  open Im.Scalars (₂₊ n)
  open Im.Swap n
  open SR word-setoid
  module Φ = RL.Width (₂₊ n)

  -- The swap's phase commutes past anything.
  central-λ : Central λ²±
  central-λ = central--1 F.p-1/2

  -- C6.
  c6 : Gʷ (F.CZ {n} ^ p) ≈ ε
  c6 = trans (refl' (Im.G-pow F.CZ CZ Eq.refl p))
             (twist0 V0R.order-CZ Eq.refl)

  -- C7: the two λ_p² pair off.
  c7 : Gʷ (F.SWAP {n} • F.SWAP) ≈ ε
  c7 = begin
    Gʷ F.SWAP • Gʷ F.SWAP                  ≈⟨ cong G-SWAP G-SWAP ⟩
    (N.⌜ Ex ⌝ • λ²±) • (N.⌜ Ex ⌝ • λ²±)    ≈⟨ collect _ _ central-λ ⟩
    N.⌜ Ex • Ex ⌝ • (λ²± • λ²±)            ≈⟨ cong (twist0 V0R.order-Ex Eq.refl)
                                                    (-1^-double F.p-1/2) ⟩
    ε • ε                                  ≈⟨ left-unit ⟩
    ε                                      ∎

  -- C8.
  c8 : Gʷ (F.CZ {n} • F.S F.↑) ≈ Gʷ (F.S F.↑ • F.CZ)
  c8 = twist0 V0R.comm-CZ-S↑ Eq.refl

  -- C9: CZ (M_g ⊗ I) = (M_g ⊗ I) CZ^g.  The multiplier's scalar is the
  -- same on both sides, and the gate parts have the same phase: the
  -- multiplier's, CZ being Pauli-free.
  c9 : Gʷ (F.CZ {n} • F.Mg F.↑) ≈ Gʷ (F.Mg F.↑ • F.CZ^ g)
  c9 = begin
    N.⌜ CZ ⌝ • Gʷ (F.Mg F.↑)
      ≈⟨ cright G-M↑ ⟩
    N.⌜ CZ ⌝ • (N.⌜ FQR.XMg ↑ ⌝ • s)
      ≈⟨ sym assoc ⟩
    N.⌜ CZ • FQR.XMg ↑ ⌝ • s
      ≈⟨ cleft lift0 (₂₊ n) (PB.sym (fq FQR.semi-M↑CZ)) same-phase ⟩
    N.⌜ FQR.XMg ↑ • CZ^ g ⌝ • s
      ≈⟨ assoc ⟩
    N.⌜ FQR.XMg ↑ ⌝ • (N.⌜ CZ^ g ⌝ • s)
      ≈⟨ cright cs _ ⟩
    N.⌜ FQR.XMg ↑ ⌝ • (s • N.⌜ CZ^ g ⌝)
      ≈⟨ sym assoc ⟩
    (N.⌜ FQR.XMg ↑ ⌝ • s) • N.⌜ CZ^ g ⌝
      ≈⟨ sym (cong G-M↑ (refl' (Im.G-CZ^ g))) ⟩
    Gʷ (F.Mg F.↑ • F.CZ^ g)
      ∎
    where
    module M1 = Im.Multiplier n
    s = Sg.sign g′ • ωℤ (F.M-phase g′)

    cs : Central s
    cs = central-• (central-sign g′) (central-ω (toℕ (F.M-phase g′)))

    -- The multiplier, one wire up: its scalar does not see the shift.
    G-M↑ : Gʷ (F.Mg {n} F.↑) ≈ N.⌜ FQR.XMg ↑ ⌝ • s
    G-M↑ = begin
      Gʷ (F.Mg F.↑)                        ≡⟨ T.G-↑ F.Mg ⟩
      ⇑ (Gʷ F.Mg)                          ≈⟨ T.lemma-shift (M1.G-M g′) ⟩
      ⇑ (N.⌜ FQR.XMg ⌝ • M1.M-scalar g′)
        ≡⟨ Eq.cong₂ _•_ (T.⇑-⌜⌝ FQR.XMg)
             (Eq.cong₂ _•_ (Im.Scalars.⇑-sign-by (₁₊ n) _)
                           (Im.Scalars.⇑-ω^ (₁₊ n) _)) ⟩
      N.⌜ FQR.XMg ↑ ⌝ • s                  ∎

    -- Both sides carry the phase of XMg ↑: CZ and CZ^g are Pauli-free.
    same-phase : Φ.Φ (CZ • FQR.XMg ↑) ≡ Φ.Φ (FQR.XMg ↑ • CZ^ g)
    same-phase =
      Eq.trans (Φ.Φ-•-freeˡ CZ (FQR.XMg ↑) Eq.refl (Φ.Φ-gate _))
        (Eq.sym (Φ.Φ-•-freeʳ (FQR.XMg ↑) (CZ^ g)
                   (proj₁ zCZ^g) (proj₂ zCZ^g)))
      where
      zCZ^g = Φ.zeroP (CZ^ g) (Φ.zeroP-^ CZ Eq.refl (toℕ g))

  -- C10, C11: the swap's phase rides along.
  semi-Ex : ∀ (a : Word (Gen (₂₊ n))) (b : Word (Gen (₂₊ n))) →
            N.⌜ Ex • a ⌝ ≈ N.⌜ b • Ex ⌝ →
            Gʷ (F.SWAP {n}) • N.⌜ a ⌝ ≈ N.⌜ b ⌝ • Gʷ F.SWAP
  semi-Ex a b e = begin
    Gʷ F.SWAP • N.⌜ a ⌝               ≈⟨ cleft G-SWAP ⟩
    (N.⌜ Ex ⌝ • λ²±) • N.⌜ a ⌝        ≈⟨ assoc ⟩
    N.⌜ Ex ⌝ • (λ²± • N.⌜ a ⌝)        ≈⟨ cright sym (central-λ _) ⟩
    N.⌜ Ex ⌝ • (N.⌜ a ⌝ • λ²±)        ≈⟨ sym assoc ⟩
    N.⌜ Ex • a ⌝ • λ²±                ≈⟨ cleft e ⟩
    N.⌜ b • Ex ⌝ • λ²±                ≈⟨ assoc ⟩
    N.⌜ b ⌝ • (N.⌜ Ex ⌝ • λ²±)        ≈⟨ cright sym G-SWAP ⟩
    N.⌜ b ⌝ • Gʷ F.SWAP               ∎

  c10 : Gʷ (F.SWAP {n} • F.S F.↑) ≈ Gʷ (F.S F.↓ • F.SWAP)
  c10 = semi-Ex (S ↑) S (twist0 V0R.semi-Ex-S↑ Eq.refl)

  c11 : Gʷ (F.SWAP {n} • F.H F.↑) ≈ Gʷ (F.H F.↓ • F.SWAP)
  c11 = semi-Ex (H ↑) H (twist0 V0R.semi-Ex-H↑ Eq.refl)

  -- C12: the gate words of Paper-V0's blake-c12, verbatim.
  c12 : Gʷ ((F.S {n} ^ p-1) F.↑ • (F.S ^ p-1) F.↓ • F.CX ^ p-1 • F.S F.↓ • F.CX)
        ≈ Gʷ (F.CZ {n})
  c12 = trans (refl' shape) (twist0 V0R.blake-c12 Eq.refl)
    where
    shape : Gʷ ((F.S {n} ^ p-1) F.↑ • (F.S ^ p-1) F.↓ • F.CX ^ p-1
                • F.S F.↓ • F.CX)
            ≡ N.⌜ (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX ⌝
    shape =
      Eq.cong₂ _•_ (Im.G-↑ (F.S ^ p-1) (S ^ p-1) (Im.G-pow F.S S Eq.refl p-1))
        (Eq.cong₂ _•_ (Im.G-pow F.S S Eq.refl p-1)
          (Eq.cong₂ _•_ (Im.G-pow F.CX CX Eq.refl p-1) Eq.refl))

------------------------------------------------------------------------
-- Three qudits

module Three (n : ℕ) where

  open T.Algebra (₃₊ n)
  open Im.Scalars (₃₊ n)
  open SR word-setoid
  module W₂ = Im.Swap (₁₊ n)

  λ²± : Word (Alph (₃₊ n))
  λ²± = N.-1± ^ F.p-1/2

  central-λ : Central λ²±
  central-λ = central--1 F.p-1/2

  -- The swap, on the bottom two wires and on the top two.
  G-SWAP↓ : Gʷ (F.SWAP {₁₊ n}) ≈ N.⌜ Ex ⌝ • λ²±
  G-SWAP↓ = W₂.G-SWAP

  G-SWAP↑ : Gʷ ((F.SWAP {n}) F.↑) ≈ N.⌜ Ex ↑ ⌝ • λ²±
  G-SWAP↑ = begin
    Gʷ (F.SWAP F.↑)                         ≡⟨ T.G-↑ F.SWAP ⟩
    ⇑ (Gʷ F.SWAP)
      ≈⟨ T.lemma-shift (Im.Swap.G-SWAP n) ⟩
    ⇑ (N.⌜ Ex ⌝ • Im.Swap.λ²± n)
      ≡⟨ Eq.cong₂ _•_ (T.⇑-⌜⌝ Ex) (Im.Scalars.⇑--1^ (₂₊ n) F.p-1/2) ⟩
    N.⌜ Ex ↑ ⌝ • λ²±                        ∎

  -- Three swaps on each side, so three λ_p² on each side.
  c13 : Gʷ ((F.SWAP {n}) F.↑ • F.SWAP F.↓ • F.SWAP F.↑)
        ≈ Gʷ (F.SWAP F.↓ • F.SWAP F.↑ • F.SWAP F.↓)
  c13 = begin
    Gʷ (F.SWAP F.↑) • (Gʷ F.SWAP • Gʷ (F.SWAP F.↑))
      ≈⟨ cong G-SWAP↑ (cong G-SWAP↓ G-SWAP↑) ⟩
    (N.⌜ Ex ↑ ⌝ • λ²±) • ((N.⌜ Ex ⌝ • λ²±) • (N.⌜ Ex ↑ ⌝ • λ²±))
      ≈⟨ cright collect _ _ central-λ ⟩
    (N.⌜ Ex ↑ ⌝ • λ²±) • (N.⌜ Ex • Ex ↑ ⌝ • (λ²± • λ²±))
      ≈⟨ collect _ _ central-λ ⟩
    N.⌜ Ex ↑ • Ex • Ex ↑ ⌝ • (λ²± • (λ²± • λ²±))
      ≈⟨ cleft twist0 V0R.yang-baxter Eq.refl ⟩
    N.⌜ Ex • Ex ↑ • Ex ⌝ • (λ²± • (λ²± • λ²±))
      ≈⟨ sym (collect _ _ central-λ) ⟩
    (N.⌜ Ex ⌝ • λ²±) • (N.⌜ Ex ↑ • Ex ⌝ • (λ²± • λ²±))
      ≈⟨ cright sym (collect _ _ central-λ) ⟩
    (N.⌜ Ex ⌝ • λ²±) • ((N.⌜ Ex ↑ ⌝ • λ²±) • (N.⌜ Ex ⌝ • λ²±))
      ≈⟨ sym (cong G-SWAP↓ (cong G-SWAP↑ G-SWAP↓)) ⟩
    Gʷ F.SWAP • (Gʷ (F.SWAP F.↑) • Gʷ F.SWAP)
      ∎

  -- Two swaps on each side.
  c14 : Gʷ ((F.SWAP {₁₊ n}) F.↓ • F.SWAP F.↑ • F.CZ F.↓)
        ≈ Gʷ (F.CZ F.↑ • F.SWAP F.↓ • F.SWAP F.↑)
  c14 = begin
    Gʷ F.SWAP • (Gʷ (F.SWAP F.↑) • N.⌜ CZ ⌝)
      ≈⟨ cong G-SWAP↓ (cleft G-SWAP↑) ⟩
    (N.⌜ Ex ⌝ • λ²±) • ((N.⌜ Ex ↑ ⌝ • λ²±) • N.⌜ CZ ⌝)
      ≈⟨ cright trail ⟩
    (N.⌜ Ex ⌝ • λ²±) • (N.⌜ Ex ↑ • CZ ⌝ • λ²±)
      ≈⟨ collect _ _ central-λ ⟩
    N.⌜ Ex • Ex ↑ • CZ ⌝ • (λ²± • λ²±)
      ≈⟨ cleft twist0 V0R.cz-slide Eq.refl ⟩
    N.⌜ CZ ↑ • Ex • Ex ↑ ⌝ • (λ²± • λ²±)
      ≈⟨ assoc ⟩
    N.⌜ CZ ↑ ⌝ • (N.⌜ Ex • Ex ↑ ⌝ • (λ²± • λ²±))
      ≈⟨ cright sym (collect _ _ central-λ) ⟩
    N.⌜ CZ ↑ ⌝ • ((N.⌜ Ex ⌝ • λ²±) • (N.⌜ Ex ↑ ⌝ • λ²±))
      ≈⟨ sym (cright cong G-SWAP↓ G-SWAP↑) ⟩
    N.⌜ CZ ↑ ⌝ • (Gʷ F.SWAP • Gʷ (F.SWAP F.↑))
      ∎
    where
    -- (a • s) • b ≈ (a • b) • s, s central.
    trail : (N.⌜ Ex ↑ ⌝ • λ²±) • N.⌜ CZ ⌝ ≈ N.⌜ Ex ↑ • CZ ⌝ • λ²±
    trail = trans assoc (trans (cright sym (central-λ _)) (sym assoc))

  -- C15: CIZ is CZ02 up to its two λ_p², which pair off.
  c15 : Gʷ ((F.CZ {₁₊ n}) F.↓ • F.CX F.↑)
        ≈ Gʷ (F.CIZ • F.CX F.↑ • F.CZ F.↓)
  c15 = begin
    N.⌜ CZ • CX ↑ ⌝
      ≈⟨ twist0 V0R.semi-CX↑-CZ↓ Eq.refl ⟩
    N.⌜ CZ02 ⌝ • N.⌜ CX ↑ • CZ ⌝
      ≈⟨ cleft sym G-CIZ ⟩
    Gʷ F.CIZ • N.⌜ CX ↑ • CZ ⌝
      ∎
    where
    G-CIZ : Gʷ (F.CIZ {n}) ≈ N.⌜ CZ02 ⌝
    G-CIZ = begin
      Gʷ F.SWAP • (N.⌜ CZ ↑ ⌝ • Gʷ F.SWAP)
        ≈⟨ cong G-SWAP↓ (cright G-SWAP↓) ⟩
      (N.⌜ Ex ⌝ • λ²±) • (N.⌜ CZ ↑ ⌝ • (N.⌜ Ex ⌝ • λ²±))
        ≈⟨ cright sym assoc ⟩
      (N.⌜ Ex ⌝ • λ²±) • (N.⌜ CZ ↑ • Ex ⌝ • λ²±)
        ≈⟨ collect _ _ central-λ ⟩
      N.⌜ CZ02 ⌝ • (λ²± • λ²±)
        ≈⟨ cright -1^-double F.p-1/2 ⟩
      N.⌜ CZ02 ⌝ • ε
        ≈⟨ right-unit ⟩
      N.⌜ CZ02 ⌝
        ∎

------------------------------------------------------------------------
-- The structural rules

-- A word shifted up past a one-wire gate: a scalar letter by
-- centrality, a gate letter by Paper-V0's comm₁.
shifted-comm₁ : (h : SympGate 1) (w : Word (Alph n)) →
                ⇑ w • N.⌜ [ FQ.gate₁ h ]ʷ ⌝ ≈± N.⌜ [ FQ.gate₁ h ]ʷ ⌝ • ⇑ w
shifted-comm₁ {n} h [ inj₁ (inj₁ tt) ]ʷ =
  PB.sym (T.Algebra.ω-central (₁₊ n) N.⌜ [ FQ.gate₁ h ]ʷ ⌝)
shifted-comm₁ h [ inj₁ (inj₂ x) ]ʷ = twist0 (V0R.comm₁ h x) Eq.refl
shifted-comm₁ {n} h [ inj₂ tt ]ʷ =
  PB.sym (T.Algebra.-1-central (₁₊ n) N.⌜ [ FQ.gate₁ h ]ʷ ⌝)
shifted-comm₁ h ε = PB.trans PB.left-unit (PB.sym PB.right-unit)
shifted-comm₁ h (u • v) =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (shifted-comm₁ h v))
      (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (shifted-comm₁ h u) PB.refl) PB.assoc)))

-- … and twice shifted, past CZ.
shifted-comm₂ : (w : Word (Alph n)) →
                ⇑ (⇑ w) • N.⌜ CZ ⌝ ≈± N.⌜ CZ ⌝ • ⇑ (⇑ w)
shifted-comm₂ {n} [ inj₁ (inj₁ tt) ]ʷ =
  PB.sym (T.Algebra.ω-central (₂₊ n) N.⌜ CZ ⌝)
shifted-comm₂ [ inj₁ (inj₂ x) ]ʷ = twist0 (V0R.comm₂ CZ-gate x) Eq.refl
shifted-comm₂ {n} [ inj₂ tt ]ʷ =
  PB.sym (T.Algebra.-1-central (₂₊ n) N.⌜ CZ ⌝)
shifted-comm₂ ε = PB.trans PB.left-unit (PB.sym PB.right-unit)
shifted-comm₂ (u • v) =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (shifted-comm₂ v))
      (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (shifted-comm₂ u) PB.refl) PB.assoc)))

------------------------------------------------------------------------
-- new is well defined

new-ax : ∀ {u v} → n F.Fig1, u === v → Gʷ u ≈± Gʷ v
new-ax F.c0          = c0
new-ax (F.c1 {n})    = One.c1 n
new-ax (F.c2 {n})    = One.c2 n
new-ax (F.c3 {n} k)  = One.c3 n k
new-ax (F.c4 {n})    = One.c4 n
new-ax (F.c5 {n})    = One.c5 n
new-ax (F.c6 {n})    = Two.c6 n
new-ax (F.c7 {n})    = Two.c7 n
new-ax (F.c8 {n})    = Two.c8 n
new-ax (F.c9 {n})    = Two.c9 n
new-ax (F.c10 {n})   = Two.c10 n
new-ax (F.c11 {n})   = Two.c11 n
new-ax (F.c12 {n})   = Two.c12 n
new-ax (F.c13 {n})   = Three.c13 n
new-ax (F.c14 {n})   = Three.c14 n
new-ax (F.c15 {n})   = Three.c15 n

new-well-defined : ∀ {u v} → (F._F,_===_ n) u v → Gʷ u ≈± Gʷ v
new-well-defined (F.srel r) = new-ax r
new-well-defined (F.cong↑ {w = u} {v = v} r) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (T.G-↑ u)) (Eq.sym (T.G-↑ v))
            (T.lemma-shift (new-well-defined r))
new-well-defined (F.comm₁ F.H-gate y) = shifted-comm₁ H-gate (new y)
new-well-defined (F.comm₁ F.S-gate y) = shifted-comm₁ S-gate (new y)
new-well-defined (F.comm₂ F.CZ-gate y) = shifted-comm₂ (new y)
new-well-defined (F.ω↑=ω F.ν-gate) = PB.refl
