------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1 mod scalars lifts to Figure 1, up to a power of -ω.
--
-- ModScalar.Syntactics is Figure 1 of arXiv:2609.40106 with every
-- scalar erased: rules C1–C15 over Symplectic's gates, with T1's
-- multiplier stripped of its phase (a/p)_L · ω^(…) and T4's swap
-- stripped of its λ_p².  This file goes back the other way.  Relabel a
-- Symplectic circuit as a Figure-1 circuit (Translation.E); then every
-- derivation of the erased rule set is a derivation of Figure 1 up to
-- a scalar,
--
--     u ≈ v  mod scalars   ⟹   E u ≈ (-ω)^a • E v  in Figure 1,
--
-- for some a : ℕ (lift-fq), and since ModScalar.Iso transports Paper-V0
-- into the erased rule set, so is every derivation of Paper-V0
-- (lift-v0).
--
-- How.  Write u ∼ v for ∃ a. u ≈ (-ω)^a • v.  Since -ω is central
-- (ν-central) and of finite order (C0: (-ω)^(2p) = 1), ∼ is an
-- equivalence and a congruence; since (-ω) ↑ = -ω is a structural rule
-- it is preserved by the shift too.  Every scalar word of Figure 1 is
-- a power of -ω, so ∼ forgets it: (a/p)_L, ω^t and λ_p² are all ∼ ε.
-- Two comparisons then carry the whole translation:
--
--   * M∼    M_a ∼ E (XM a) — T1 is XM a followed by its scalar, once
--           T1's Z-exponent (1-a)/(2a) is seen to be Paper-V1's
--           (a⁻¹ - 1)/2 (Z-exponent);
--   * SWAP∼ SWAP ∼ E Ex   — T4 is the swap followed by λ_p².
--
-- Each axiom of the erased rule set is the matching Figure-1 rule read
-- through these two, through E commuting with powers (wmap-^) and with
-- the shift (E-↑), and, for C5 and C9, read backwards.  The induction
-- over a derivation is then just the congruence properties of ∼.
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

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Lift
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Properties.Ring (+-*-ring p-2) using (-‿distribˡ-*)
import Data.Nat as Nat
open import Data.Product using (proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP

open Primitive-Root-Modp' g* g-gen using (g′ ; g^_)

import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen as F
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Syntactics
  p-3 p-prime g* g-gen as FQ
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Iso
  p-3 p-prime g* g-gen as FQIso
import Examples.Groups.Clifford+MinusOne.Qupit.Translation
  p-3 p-prime g* g-gen as T
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as V0

module FQR = FQ.Clifford-Relations
module V0R = V0.Clifford-Relations

open F using (ν ; _≈ᶠ_)
open T using (E ; sym→fig ; gate→ ; wmap-^ ; E-↑)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Equality up to a power of -ω

infix 4 _∼_
_∼_ : Word (F.Gen n) → Word (F.Gen n) → Set
u ∼ v = ∃ λ (a : ℕ) → u ≈ᶠ (ν ^ a • v)

-- The exponent that undoes a: a + ν⁻ a is (p + p) · a on the nose,
-- since p is 1 + p-1.
ν⁻ : ℕ → ℕ
ν⁻ a = (p-1 Nat.+ p) Nat.* a

module _ {n : ℕ} where

  open PB (F._F,_===_ n)
  open PP (F._F,_===_ n) using (word-setoid ; ^-+ ; ^^ ; ^-cong ; ε^k=ε)

  -- (-ω)^(ν⁻ a) inverts (-ω)^a, by C0.
  ν^-inverse : ∀ a → ν {n} ^ ν⁻ a • ν ^ a ≈ ε
  ν^-inverse a = begin
    ν ^ ν⁻ a • ν ^ a           ≈⟨ F.ν^-central (ν⁻ a) (ν ^ a) ⟩
    ν ^ a • ν ^ ν⁻ a           ≈⟨ sym (^-+ ν a (ν⁻ a)) ⟩
    ν ^ ((p Nat.+ p) Nat.* a)  ≈⟨ sym (^^ ν (p Nat.+ p) a) ⟩
    (ν ^ (p Nat.+ p)) ^ a      ≈⟨ ^-cong _ _ a (axiom (F.srel F.c0)) ⟩
    ε ^ a                      ≈⟨ ε^k=ε a ⟩
    ε                          ∎
    where open SR word-setoid

  --------------------------------------------------------------------
  -- ∼ is an equivalence and a congruence

  ∼-refl : ∀ {u : Word (F.Gen n)} → u ∼ u
  ∼-refl = 0 , sym left-unit

  ≈⇒∼ : ∀ {u v : Word (F.Gen n)} → u ≈ v → u ∼ v
  ≈⇒∼ h = 0 , trans h (sym left-unit)

  ≡⇒∼ : ∀ {u v : Word (F.Gen n)} → u ≡ v → u ∼ v
  ≡⇒∼ e = ≈⇒∼ (refl' e)

  ∼-sym : ∀ {u v : Word (F.Gen n)} → u ∼ v → v ∼ u
  ∼-sym {u} {v} (a , h) = ν⁻ a , (begin
    v                          ≈⟨ sym left-unit ⟩
    ε • v                      ≈⟨ cong (sym (ν^-inverse a)) refl ⟩
    (ν ^ ν⁻ a • ν ^ a) • v     ≈⟨ assoc ⟩
    ν ^ ν⁻ a • (ν ^ a • v)     ≈⟨ cong refl (sym h) ⟩
    ν ^ ν⁻ a • u               ∎)
    where open SR word-setoid

  ∼-trans : ∀ {u v w : Word (F.Gen n)} → u ∼ v → v ∼ w → u ∼ w
  ∼-trans {u} {v} {w} (a , h) (b , k) = a Nat.+ b , (begin
    u                          ≈⟨ h ⟩
    ν ^ a • v                  ≈⟨ cong refl k ⟩
    ν ^ a • (ν ^ b • w)        ≈⟨ sym assoc ⟩
    (ν ^ a • ν ^ b) • w        ≈⟨ cong (sym (^-+ ν a b)) refl ⟩
    ν ^ (a Nat.+ b) • w        ∎)
    where open SR word-setoid

  -- The scalars of the two factors are collected at the front, the
  -- second one walked across v by centrality.
  ∼-cong : ∀ {u v u' v' : Word (F.Gen n)} →
           u ∼ v → u' ∼ v' → u • u' ∼ v • v'
  ∼-cong {u} {v} {u'} {v'} (a , h) (b , k) = a Nat.+ b , (begin
    u • u'                     ≈⟨ cong h k ⟩
    (ν ^ a • v) • (ν ^ b • v') ≈⟨ assoc ⟩
    ν ^ a • (v • (ν ^ b • v')) ≈⟨ cong refl (sym assoc) ⟩
    ν ^ a • ((v • ν ^ b) • v') ≈⟨ cong refl (cong (sym (central b v)) refl) ⟩
    ν ^ a • ((ν ^ b • v) • v') ≈⟨ cong refl assoc ⟩
    ν ^ a • (ν ^ b • (v • v')) ≈⟨ sym assoc ⟩
    (ν ^ a • ν ^ b) • (v • v') ≈⟨ cong (sym (^-+ ν a b)) refl ⟩
    ν ^ (a Nat.+ b) • (v • v') ∎)
    where
    open SR word-setoid
    central = F.ν^-central

  ∼-^ : ∀ {u v : Word (F.Gen n)} → u ∼ v → ∀ k → u ^ k ∼ v ^ k
  ∼-^ h ₀       = ∼-refl
  ∼-^ h (₁₊ ₀)  = h
  ∼-^ h (₂₊ k)  = ∼-cong h (∼-^ h (₁₊ k))

  ∼-setoid : Setoid 0ℓ 0ℓ
  ∼-setoid = record
    { Carrier       = Word (F.Gen n)
    ; _≈_           = _∼_
    ; isEquivalence = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }
    }

  -- A rule of Figure 1, reached and left up to scalars.
  via : ∀ {u u' v' v : Word (F.Gen n)} → u ∼ u' → u' ≈ v' → v' ∼ v → u ∼ v
  via h r k = ∼-trans h (∼-trans (≈⇒∼ r) k)

  --------------------------------------------------------------------
  -- The scalar words are ∼ ε

  ν^∼ε : ∀ a → _∼_ {n} (ν ^ a) ε
  ν^∼ε a = a , sym right-unit

  •∼ε : ∀ {s t : Word (F.Gen n)} → s ∼ ε → t ∼ ε → s • t ∼ ε
  •∼ε hs ht = ∼-trans (∼-cong hs ht) (≈⇒∼ left-unit)

  ^∼ε : ∀ {s : Word (F.Gen n)} → s ∼ ε → ∀ k → s ^ k ∼ ε
  ^∼ε hs k = ∼-trans (∼-^ hs k) (≈⇒∼ (ε^k=ε k))

  -- … and so can be dropped from the end of a word.
  dropʳ : ∀ {w s : Word (F.Gen n)} → s ∼ ε → w • s ∼ w
  dropʳ hs = ∼-trans (∼-cong ∼-refl hs) (≈⇒∼ right-unit)

  -1ˢ∼ε : _∼_ {n} F.-1ˢ ε
  -1ˢ∼ε = ν^∼ε p

  ω^∼ε : ∀ t → _∼_ {n} (F.ω^ t) ε
  ω^∼ε t = ^∼ε (ν^∼ε (₁₊ p)) (toℕ t)

  λ²∼ε : _∼_ {n} F.λ² ε
  λ²∼ε = ^∼ε -1ˢ∼ε F.p-1/2

  legendre∼ε : ∀ a* → _∼_ {n} (F.legendre a*) ε
  legendre∼ε a* = by (F.is-one (toℕ (a* .proj₁ ^′ F.p-1/2)))
    where
    by : ∀ {y : ℤ ₚ} (d : Dec (toℕ y ≡ 1)) → _∼_ {n} (F.legendre-by d) ε
    by (yes _) = ∼-refl
    by (no _)  = -1ˢ∼ε

------------------------------------------------------------------------
-- The shift

ν^↑ : ∀ k → (ν {n} ^ k) F.↑ ≈ᶠ ν ^ k
ν^↑ {n} k =
  PB.trans (PB.refl' _ (wmap-^ F._↥ ν k))
           (PP.^-cong (F._F,_===_ (₁₊ n)) (ν F.↑) ν k F.ν↑≈ν)

∼-↑ : ∀ {u v : Word (F.Gen n)} → u ∼ v → u F.↑ ∼ v F.↑
∼-↑ {n} {u} {v} (a , h) =
  a , PB.trans (F.lemma-cong↑ u (ν ^ a • v) h) (PB.cong (ν^↑ a) PB.refl)

------------------------------------------------------------------------
-- E on powers
--
-- E is a wmap, so it commutes with powers; the Paulis and S⁻¹ are
-- spelled alike on both sides.

E-S^ : ∀ (k : ℤ ₚ) → E (FQ.S^ {n} k) ≡ F.S^ k
E-S^ k = wmap-^ sym→fig FQ.S (toℕ k)

E-CZ^ : ∀ (k : ℤ ₚ) → E (FQ.CZ^ {n} k) ≡ F.CZ^ k
E-CZ^ k = wmap-^ sym→fig FQ.CZ (toℕ k)

E-Z : E (FQR.Z {n}) ≡ F.Z
E-Z = Eq.cong (λ t → F.H • F.H • F.S • F.H • F.H • t)
              (wmap-^ sym→fig FQ.S p-1)

E-X : E (FQR.X {n}) ≡ F.X
E-X = Eq.cong (λ t → F.H • F.S • F.H • F.H • t • F.H)
              (wmap-^ sym→fig FQ.S p-1)

E-Z^ : ∀ (k : ℤ ₚ) → E (FQR.Z^ k {n}) ≡ F.Z^ k
E-Z^ k = Eq.trans (wmap-^ sym→fig FQR.Z (toℕ k)) (Eq.cong (_^ toℕ k) E-Z)

E-X^ : ∀ (k : ℤ ₚ) → E (FQR.X^ k {n}) ≡ F.X^ k
E-X^ k = Eq.trans (wmap-^ sym→fig FQR.X (toℕ k)) (Eq.cong (_^ toℕ k) E-X)

------------------------------------------------------------------------
-- T1 is XM followed by a scalar

-- T1 writes the Z-exponent (1-a)/(2a), Paper-V1 (a⁻¹ - 1)/2: the same
-- element of ℤ/pℤ, by a · a⁻¹ = 1.
Z-exponent : ∀ (a* : ℤ* ₚ) →
             let a = a* .proj₁ ; a⁻¹ = (a* ⁻¹) .proj₁ in
             (a⁻¹ + - ₁) * FQ.1/2 ≡ F.M-Z-exponent a*
Z-exponent a* = begin
  (a⁻¹ + - ₁) * h
    ≡⟨ Eq.cong (λ t → (a⁻¹ + - t) * h) (Eq.sym aa⁻¹) ⟩
  (a⁻¹ + - (a * a⁻¹)) * h
    ≡⟨ Eq.cong (λ t → (a⁻¹ + t) * h) (-‿distribˡ-* a a⁻¹) ⟩
  (a⁻¹ + - a * a⁻¹) * h
    ≡⟨ Eq.cong (λ t → (t + - a * a⁻¹) * h) (Eq.sym (*-identityˡ a⁻¹)) ⟩
  (₁ * a⁻¹ + - a * a⁻¹) * h
    ≡⟨ Eq.cong (_* h) (Eq.sym (*-distribʳ-+ a⁻¹ ₁ (- a))) ⟩
  (₁ + - a) * a⁻¹ * h
    ≡⟨ *-assoc (₁ + - a) a⁻¹ h ⟩
  (₁ + - a) * (a⁻¹ * h)
    ≡⟨ Eq.cong ((₁ + - a) *_) (*-comm a⁻¹ h) ⟩
  (₁ + - a) * (h * a⁻¹)
    ≡⟨ Eq.sym (*-assoc (₁ + - a) h a⁻¹) ⟩
  (₁ + - a) * h * a⁻¹
    ∎
  where
  open Eq.≡-Reasoning
  a = a* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁
  h = F.1/2
  aa⁻¹ : a * a⁻¹ ≡ ₁
  aa⁻¹ = lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}}

-- T1's gates, without its scalar.
M-gates : ℤ* ₚ → Word (F.Gen (₁₊ n))
M-gates a* =
  F.Z^ (F.M-Z-exponent a*) • F.X^ ((₁ + - a) * F.1/2)
  • F.S^ a⁻¹ • F.H • F.S^ a • F.H • F.S^ a⁻¹ • F.H
  where
  a = a* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁

E-XM : ∀ (a* : ℤ* ₚ) → E (FQR.XM {n} a*) ≡ M-gates a*
E-XM a* =
  Eq.cong₂ _•_ (Eq.trans (E-Z^ ((a⁻¹ + - ₁) * FQ.1/2))
                         (Eq.cong F.Z^ (Z-exponent a*)))
  (Eq.cong₂ _•_ (E-X^ ((₁ + - a) * FQ.1/2))
  (Eq.cong₂ _•_ (E-S^ a⁻¹)
  (Eq.cong (F.H •_)
  (Eq.cong₂ _•_ (E-S^ a)
  (Eq.cong (F.H •_)
  (Eq.cong₂ _•_ (E-S^ a⁻¹) Eq.refl))))))
  where
  a = a* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁

M≈gates : ∀ (a* : ℤ* ₚ) →
          F.M {n} a* ≈ᶠ M-gates a* • (F.legendre a* • F.ω^ (F.M-phase a*))
M≈gates {n} a* =
  by-passoc (□ • □ • □ • □ • □ • □ • □ • □ • □)
            ((□ • □ • □ • □ • □ • □ • □ • □) • □) Eq.refl
  where open PP.Pattern-Assoc (F._F,_===_ (₁₊ n))

M∼ : ∀ (a* : ℤ* ₚ) → F.M {n} a* ∼ E (FQR.XM a*)
M∼ {n} a* = begin
  F.M a*
    ≈⟨ ≈⇒∼ (M≈gates a*) ⟩
  M-gates a* • (F.legendre a* • F.ω^ (F.M-phase a*))
    ≈⟨ dropʳ (•∼ε (legendre∼ε a*) (ω^∼ε _)) ⟩
  M-gates a*
    ≡⟨ Eq.sym (E-XM a*) ⟩
  E (FQR.XM a*)
    ∎
  where open SR (∼-setoid {₁₊ n})

------------------------------------------------------------------------
-- T4 is Ex followed by a scalar

SWAP≈ : F.SWAP {n} ≈ᶠ E FQ.Ex • F.λ²
SWAP≈ {n} =
  by-passoc (□ • □ • □ • □ • □ • □ • □ • □ • □ • □)
            ((□ • □ • □ • □ • □ • □ • □ • □ • □) • □) Eq.refl
  where open PP.Pattern-Assoc (F._F,_===_ (₂₊ n))

SWAP∼Ex : F.SWAP {n} ∼ E FQ.Ex
SWAP∼Ex = ∼-trans (≈⇒∼ SWAP≈) (dropʳ λ²∼ε)

Ex∼SWAP : E (FQ.Ex {n}) ∼ F.SWAP
Ex∼SWAP = ∼-sym SWAP∼Ex

------------------------------------------------------------------------
-- The axioms

-- C12 is the same word on both sides once E has passed the powers.
private
  E-c12 : E {₂₊ n} ((FQ.S ^ p-1) FQ.↑ • (FQ.S ^ p-1) • FQ.CX ^ p-1
                    • FQ.S • FQ.CX)
          ≡ (F.S ^ p-1) F.↑ • (F.S ^ p-1) • F.CX ^ p-1 • F.S • F.CX
  E-c12 =
    Eq.cong₂ _•_
      (Eq.trans (E-↑ (FQ.S ^ p-1)) (Eq.cong F._↑ (wmap-^ sym→fig FQ.S p-1)))
      (Eq.cong₂ _•_ (wmap-^ sym→fig FQ.S p-1)
        (Eq.cong (_• (F.S • F.CX)) (wmap-^ sym→fig FQ.CX p-1)))

lift-ax : ∀ {n} {u v : Word (FQ.Gen n)} → n FQR.QRel, u === v →
          ∃ λ (a : ℕ) → E u ≈ᶠ (ν ^ a • E v)
-- One wire.
lift-ax FQR.order-S =
  ≈⇒∼ (PB.trans (PB.refl' _ (wmap-^ sym→fig FQ.S p)) (PB.axiom (F.srel F.c1)))
lift-ax {₁₊ n} FQR.order-H = begin
  F.H ^ 2           ≈⟨ ≈⇒∼ (PB.axiom (F.srel F.c2)) ⟩
  F.M₋₁ • F.λ²      ≈⟨ dropʳ λ²∼ε ⟩
  F.M₋₁             ≈⟨ M∼ -'₁ ⟩
  E FQR.XM₋₁        ∎
  where open SR (∼-setoid {₁₊ n})
lift-ax {₁₊ n} (FQR.M-power k) = begin
  E (FQR.XMg ^ toℕ k)   ≡⟨ wmap-^ sym→fig FQR.XMg (toℕ k) ⟩
  E FQR.XMg ^ toℕ k     ≈⟨ ∼-^ (∼-sym (M∼ g′)) (toℕ k) ⟩
  F.Mg ^ toℕ k          ≈⟨ ≈⇒∼ (PB.axiom (F.srel (F.c3 k))) ⟩
  F.M (g^ k)            ≈⟨ M∼ (g^ k) ⟩
  E (FQR.XM (g^ k))     ∎
  where open SR (∼-setoid {₁₊ n})
lift-ax {₁₊ n} FQR.semi-MS = begin
  E FQR.XMg • F.S                   ≈⟨ ∼-cong (∼-sym (M∼ g′)) ∼-refl ⟩
  F.Mg • F.S                        ≈⟨ ≈⇒∼ (PB.axiom (F.srel F.c4)) ⟩
  F.Z^ c • F.S^ d • F.Mg            ≈⟨ ∼-cong ∼-refl (∼-cong ∼-refl (M∼ g′)) ⟩
  F.Z^ c • F.S^ d • E FQR.XMg       ≡⟨ Eq.sym (Eq.cong₂ _•_ (E-Z^ c)
                                         (Eq.cong (_• E FQR.XMg) (E-S^ d))) ⟩
  E (FQR.Z^ c • FQ.S^ d • FQR.XMg)  ∎
  where
  open SR (∼-setoid {₁₊ n})
  d = F.g⁻¹ * F.g⁻¹
  c = (₁ + - g) * F.1/2 * d
lift-ax FQR.comm-HHSHHS = ≈⇒∼ (PB.sym (PB.axiom (F.srel F.c5)))
-- Two wires.
lift-ax FQR.order-CZ =
  ≈⇒∼ (PB.trans (PB.refl' _ (wmap-^ sym→fig FQ.CZ p)) (PB.axiom (F.srel F.c6)))
lift-ax FQR.order-Ex =
  via (∼-cong Ex∼SWAP Ex∼SWAP) (PB.axiom (F.srel F.c7)) ∼-refl
lift-ax FQR.comm-CZ-S↑ = ≈⇒∼ (PB.axiom (F.srel F.c8))
lift-ax {₂₊ n} FQR.semi-M↑CZ = begin
  E (FQR.XMg FQ.↑) • E (FQ.CZ^ g)  ≡⟨ Eq.cong₂ _•_ (E-↑ FQR.XMg) (E-CZ^ g) ⟩
  E FQR.XMg F.↑ • F.CZ^ g          ≈⟨ ∼-cong (∼-↑ (∼-sym (M∼ g′))) ∼-refl ⟩
  F.Mg F.↑ • F.CZ^ g               ≈⟨ ≈⇒∼ (PB.sym (PB.axiom (F.srel F.c9))) ⟩
  F.CZ • F.Mg F.↑                  ≈⟨ ∼-cong ∼-refl (∼-↑ (M∼ g′)) ⟩
  F.CZ • E FQR.XMg F.↑             ≡⟨ Eq.cong (F.CZ •_) (Eq.sym (E-↑ FQR.XMg)) ⟩
  F.CZ • E (FQR.XMg FQ.↑)          ∎
  where open SR (∼-setoid {₂₊ n})
lift-ax FQR.semi-Ex-S↑ =
  via (∼-cong Ex∼SWAP ∼-refl) (PB.axiom (F.srel F.c10)) (∼-cong ∼-refl SWAP∼Ex)
lift-ax FQR.semi-Ex-H↑ =
  via (∼-cong Ex∼SWAP ∼-refl) (PB.axiom (F.srel F.c11)) (∼-cong ∼-refl SWAP∼Ex)
lift-ax FQR.blake-c12 =
  ≈⇒∼ (PB.trans (PB.refl' _ E-c12) (PB.axiom (F.srel F.c12)))
-- Three wires.
lift-ax FQR.yang-baxter =
  via (∼-cong (∼-↑ Ex∼SWAP) (∼-cong Ex∼SWAP (∼-↑ Ex∼SWAP)))
      (PB.axiom (F.srel F.c13))
      (∼-cong SWAP∼Ex (∼-cong (∼-↑ SWAP∼Ex) SWAP∼Ex))
lift-ax FQR.cz-slide =
  via (∼-cong Ex∼SWAP (∼-cong (∼-↑ Ex∼SWAP) ∼-refl))
      (PB.axiom (F.srel F.c14))
      (∼-cong ∼-refl (∼-cong SWAP∼Ex (∼-↑ SWAP∼Ex)))
lift-ax FQR.semi-CX↑-CZ↓ =
  via ∼-refl (PB.axiom (F.srel F.c15))
      (∼-cong (∼-cong SWAP∼Ex (∼-cong ∼-refl SWAP∼Ex)) ∼-refl)
-- The structural rules.
lift-ax (FQR.comm₁ h x) = ≈⇒∼ (PB.axiom (F.comm₁ (gate→ h) (sym→fig x)))
lift-ax (FQR.comm₂ h x) = ≈⇒∼ (PB.axiom (F.comm₂ (gate→ h) (sym→fig x)))
lift-ax (FQR.cong↑ {w = u} {v = v} r) =
  Eq.subst₂ _∼_ (Eq.sym (E-↑ u)) (Eq.sym (E-↑ v)) (∼-↑ (lift-ax r))

------------------------------------------------------------------------
-- Derivations

lift-fq : ∀ n {u v : Word (FQ.Gen n)} → PB._≈_ (n FQR.QRel,_===_) u v →
          ∃ λ (a : ℕ) → E u ≈ᶠ (ν ^ a • E v)
lift-fq n PB.refl         = ∼-refl
lift-fq n (PB.sym h)      = ∼-sym (lift-fq n h)
lift-fq n (PB.trans h h') = ∼-trans (lift-fq n h) (lift-fq n h')
lift-fq n (PB.cong h h')  = ∼-cong (lift-fq n h) (lift-fq n h')
lift-fq n PB.assoc        = ≈⇒∼ PB.assoc
lift-fq n PB.left-unit    = ≈⇒∼ PB.left-unit
lift-fq n PB.right-unit   = ≈⇒∼ PB.right-unit
lift-fq n (PB.axiom r)    = lift-ax r

-- Paper-V0, through Figure 1 mod scalars.
lift-v0 : ∀ n {u v : Word (FQ.Gen n)} → PB._≈_ (n V0R.QRel,_===_) u v →
          ∃ λ (a : ℕ) → E u ≈ᶠ (ν ^ a • E v)
lift-v0 n h = lift-fq n (FQIso.Theorem.v0⇒fq n h)
