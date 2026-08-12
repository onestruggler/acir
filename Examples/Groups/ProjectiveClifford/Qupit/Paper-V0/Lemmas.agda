{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Ex-conjugation algebra of the Paper-V0 rules.
--
-- Paper-V0 axiomatises the swap directly: order-Ex says Ex is an
-- involution, and semi-Ex-S↑ / semi-Ex-H↑ say conjugating by it carries
-- a gate on the upper wire down to the lower one,
--
--     Ex • S ↑ === S • Ex        Ex • H ↑ === H • Ex.
--
-- Everything below is the bookkeeping that turns those three axioms into
-- a usable calculus: the opposite direction (a lower-wire gate goes up),
-- the two-sided conjugation forms, and the extension of all of it from
-- single gates to powers and to whole words.  These are the steps that
-- the corresponding symplectic lemmas get for free from Ex's definition
-- as a CZ/H word — a route that is NOT available here, since the
-- symplectic proofs of lemma-comm-Ex-H' and lemma-comm-Ex-H↑' run
-- through lemma-eqn16 / lemma-eqn17 / lemma-CZH↓CZCZ, i.e. through the
-- CZ-H-CZ relations c10 and c11 that Paper-V0 does not have.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
open Lemmas-Clifford using (lemma-↑^ ; lemma-↓^)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Ex is its own inverse

module Ex-Conjugation (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  -- order-Ex with the power unfolded: Ex ^ 2 is Ex • (Ex ^ 1) is
  -- Ex • Ex definitionally, so this is the axiom itself.
  lemma-Ex-Ex : Ex • Ex ≈ ε
  lemma-Ex-Ex = axiom order-Ex

  -- Cancelling a trailing Ex • Ex.
  lemma-cancel-Ex : ∀ {w} → w • Ex • Ex ≈ w
  lemma-cancel-Ex {w} = begin
    w • Ex • Ex ≈⟨ cright lemma-Ex-Ex ⟩
    w • ε       ≈⟨ right-unit ⟩
    w ∎

  ------------------------------------------------------------------------
  -- The two axioms, and their opposites
  --
  -- Conjugating by an involution is symmetric: from Ex • H ↑ ≈ H • Ex we
  -- get Ex • H ≈ H ↑ • Ex by inserting Ex • Ex on the right, pushing the
  -- axiom through backwards, and cancelling the pair on the left.

  lemma-Ex-H↑ : Ex • H ↑ ≈ H • Ex
  lemma-Ex-H↑ = axiom semi-Ex-H↑

  lemma-Ex-S↑ : Ex • S ↑ ≈ S • Ex
  lemma-Ex-S↑ = axiom semi-Ex-S↑

  lemma-Ex-H : Ex • H ≈ H ↑ • Ex
  lemma-Ex-H = begin
    Ex • H                 ≈⟨ sym lemma-cancel-Ex ⟩
    (Ex • H) • Ex • Ex     ≈⟨ by-assoc auto ⟩
    Ex • (H • Ex) • Ex     ≈⟨ cright cleft sym lemma-Ex-H↑ ⟩
    Ex • (Ex • H ↑) • Ex   ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • H ↑ • Ex   ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • H ↑ • Ex           ≈⟨ left-unit ⟩
    H ↑ • Ex ∎

  lemma-Ex-S : Ex • S ≈ S ↑ • Ex
  lemma-Ex-S = begin
    Ex • S                 ≈⟨ sym lemma-cancel-Ex ⟩
    (Ex • S) • Ex • Ex     ≈⟨ by-assoc auto ⟩
    Ex • (S • Ex) • Ex     ≈⟨ cright cleft sym lemma-Ex-S↑ ⟩
    Ex • (Ex • S ↑) • Ex   ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • S ↑ • Ex   ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • S ↑ • Ex           ≈⟨ left-unit ⟩
    S ↑ • Ex ∎

  ------------------------------------------------------------------------
  -- Two-sided conjugation
  --
  -- The form the later derivations actually use: Ex • g • Ex is g with
  -- its wire flipped.

  lemma-conj-Ex-H↑ : Ex • H ↑ • Ex ≈ H
  lemma-conj-Ex-H↑ = begin
    Ex • H ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • H ↑) • Ex ≈⟨ cleft lemma-Ex-H↑ ⟩
    (H • Ex) • Ex   ≈⟨ assoc ⟩
    H • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    H ∎

  lemma-conj-Ex-S↑ : Ex • S ↑ • Ex ≈ S
  lemma-conj-Ex-S↑ = begin
    Ex • S ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • S ↑) • Ex ≈⟨ cleft lemma-Ex-S↑ ⟩
    (S • Ex) • Ex   ≈⟨ assoc ⟩
    S • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    S ∎

  lemma-conj-Ex-H : Ex • H • Ex ≈ H ↑
  lemma-conj-Ex-H = begin
    Ex • H • Ex     ≈⟨ sym assoc ⟩
    (Ex • H) • Ex   ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • Ex ≈⟨ assoc ⟩
    H ↑ • Ex • Ex   ≈⟨ lemma-cancel-Ex ⟩
    H ↑ ∎

  lemma-conj-Ex-S : Ex • S • Ex ≈ S ↑
  lemma-conj-Ex-S = begin
    Ex • S • Ex     ≈⟨ sym assoc ⟩
    (Ex • S) • Ex   ≈⟨ cleft lemma-Ex-S ⟩
    (S ↑ • Ex) • Ex ≈⟨ assoc ⟩
    S ↑ • Ex • Ex   ≈⟨ lemma-cancel-Ex ⟩
    S ↑ ∎

  ------------------------------------------------------------------------
  -- Powers
  --
  -- Conjugation is a homomorphism, so it passes through a power one
  -- factor at a time.

  lemma-Ex-Hᵏ : ∀ k → Ex • H ^ k ≈ (H ↑) ^ k • Ex
  lemma-Ex-Hᵏ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Hᵏ ₁ = lemma-Ex-H
  lemma-Ex-Hᵏ (₂₊ k) = begin
    Ex • H ^ ₂₊ k            ≈⟨ sym assoc ⟩
    (Ex • H) • H ^ ₁₊ k      ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • H ^ ₁₊ k    ≈⟨ assoc ⟩
    H ↑ • Ex • H ^ ₁₊ k      ≈⟨ cright lemma-Ex-Hᵏ (₁₊ k) ⟩
    H ↑ • (H ↑) ^ ₁₊ k • Ex  ≈⟨ sym assoc ⟩
    (H ↑) ^ ₂₊ k • Ex ∎

  lemma-Ex-Sᵏ : ∀ k → Ex • S ^ k ≈ (S ↑) ^ k • Ex
  lemma-Ex-Sᵏ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Sᵏ ₁ = lemma-Ex-S
  lemma-Ex-Sᵏ (₂₊ k) = begin
    Ex • S ^ ₂₊ k            ≈⟨ sym assoc ⟩
    (Ex • S) • S ^ ₁₊ k      ≈⟨ cleft lemma-Ex-S ⟩
    (S ↑ • Ex) • S ^ ₁₊ k    ≈⟨ assoc ⟩
    S ↑ • Ex • S ^ ₁₊ k      ≈⟨ cright lemma-Ex-Sᵏ (₁₊ k) ⟩
    S ↑ • (S ↑) ^ ₁₊ k • Ex  ≈⟨ sym assoc ⟩
    (S ↑) ^ ₂₊ k • Ex ∎

  lemma-Ex-Hᵏ↑ : ∀ k → Ex • (H ↑) ^ k ≈ H ^ k • Ex
  lemma-Ex-Hᵏ↑ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Hᵏ↑ ₁ = lemma-Ex-H↑
  lemma-Ex-Hᵏ↑ (₂₊ k) = begin
    Ex • (H ↑) ^ ₂₊ k          ≈⟨ sym assoc ⟩
    (Ex • H ↑) • (H ↑) ^ ₁₊ k  ≈⟨ cleft lemma-Ex-H↑ ⟩
    (H • Ex) • (H ↑) ^ ₁₊ k    ≈⟨ assoc ⟩
    H • Ex • (H ↑) ^ ₁₊ k      ≈⟨ cright lemma-Ex-Hᵏ↑ (₁₊ k) ⟩
    H • H ^ ₁₊ k • Ex          ≈⟨ sym assoc ⟩
    H ^ ₂₊ k • Ex ∎

  lemma-Ex-Sᵏ↑ : ∀ k → Ex • (S ↑) ^ k ≈ S ^ k • Ex
  lemma-Ex-Sᵏ↑ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Sᵏ↑ ₁ = lemma-Ex-S↑
  lemma-Ex-Sᵏ↑ (₂₊ k) = begin
    Ex • (S ↑) ^ ₂₊ k          ≈⟨ sym assoc ⟩
    (Ex • S ↑) • (S ↑) ^ ₁₊ k  ≈⟨ cleft lemma-Ex-S↑ ⟩
    (S • Ex) • (S ↑) ^ ₁₊ k    ≈⟨ assoc ⟩
    S • Ex • (S ↑) ^ ₁₊ k      ≈⟨ cright lemma-Ex-Sᵏ↑ (₁₊ k) ⟩
    S • S ^ ₁₊ k • Ex          ≈⟨ sym assoc ⟩
    S ^ ₂₊ k • Ex ∎

  ------------------------------------------------------------------------
  -- Conjugation is a monoid homomorphism
  --
  -- Stated as "Ex • u ≈ u' • Ex", the form the chains below compose in.
  -- These two are what lift the gate-level axioms to the derived words Z,
  -- R, M and Mg, which are just products and powers of S and H.

  lemma-Ex-• : ∀ {u u' v v'} → Ex • u ≈ u' • Ex → Ex • v ≈ v' • Ex →
               Ex • (u • v) ≈ (u' • v') • Ex
  lemma-Ex-• {u} {u'} {v} {v'} eu ev = begin
    Ex • (u • v)   ≈⟨ sym assoc ⟩
    (Ex • u) • v   ≈⟨ cleft eu ⟩
    (u' • Ex) • v  ≈⟨ assoc ⟩
    u' • Ex • v    ≈⟨ cright ev ⟩
    u' • v' • Ex   ≈⟨ sym assoc ⟩
    (u' • v') • Ex ∎

  lemma-Ex-pow : ∀ {u u'} → Ex • u ≈ u' • Ex → ∀ k → Ex • u ^ k ≈ u' ^ k • Ex
  lemma-Ex-pow e ₀      = trans right-unit (sym left-unit)
  lemma-Ex-pow e ₁      = e
  lemma-Ex-pow e (₂₊ k) = lemma-Ex-• e (lemma-Ex-pow e (₁₊ k))

  ------------------------------------------------------------------------
  -- CZ is symmetric in its two wires, so conjugation leaves it alone

  lemma-Ex-CZ : Ex • CZ ≈ CZ • Ex
  lemma-Ex-CZ = axiom comm-Ex-CZ

  lemma-Ex-CZᵏ : ∀ k → Ex • CZ ^ k ≈ CZ ^ k • Ex
  lemma-Ex-CZᵏ = lemma-Ex-pow lemma-Ex-CZ

  lemma-conj-Ex-CZ : Ex • CZ • Ex ≈ CZ
  lemma-conj-Ex-CZ = begin
    Ex • CZ • Ex    ≈⟨ sym assoc ⟩
    (Ex • CZ) • Ex  ≈⟨ cleft lemma-Ex-CZ ⟩
    (CZ • Ex) • Ex  ≈⟨ assoc ⟩
    CZ • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    CZ ∎

  ------------------------------------------------------------------------
  -- The derived one-wire words, carried from the upper wire to the lower
  --
  -- Each is a product of powers of S and H, so it is assembled from the
  -- two axioms by lemma-Ex-• and lemma-Ex-pow.  The `refl'` steps are
  -- the shift commuting with a power — definitional for a literal
  -- exponent, but p-1 and toℕ k are symbolic, so lemma-↑^ is needed.

  lemma-Ex-S⁻¹↑ : Ex • S⁻¹ ↑ ≈ S⁻¹ • Ex
  lemma-Ex-S⁻¹↑ = begin
    Ex • S⁻¹ ↑          ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ p-1 S)) ⟩
    Ex • (S ↑) ^ p-1    ≈⟨ lemma-Ex-Sᵏ↑ p-1 ⟩
    S⁻¹ • Ex ∎

  lemma-Ex-Z↑ : Ex • Z ↑ ≈ Z • Ex
  lemma-Ex-Z↑ =
    lemma-Ex-• lemma-Ex-H↑
      (lemma-Ex-• lemma-Ex-H↑
        (lemma-Ex-• lemma-Ex-S↑
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• lemma-Ex-H↑ lemma-Ex-S⁻¹↑))))

  lemma-Ex-Z^↑ : ∀ k → Ex • (Z^ k) ↑ ≈ Z^ k • Ex
  lemma-Ex-Z^↑ k = begin
    Ex • (Z ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) Z)) ⟩
    Ex • (Z ↑) ^ toℕ k       ≈⟨ lemma-Ex-pow lemma-Ex-Z↑ (toℕ k) ⟩
    Z ^ toℕ k • Ex ∎

  lemma-Ex-R↑ : Ex • R ↑ ≈ R • Ex
  lemma-Ex-R↑ = lemma-Ex-• lemma-Ex-S↑ (lemma-Ex-Z^↑ 1/2)

  lemma-Ex-R^↑ : ∀ k → Ex • (R^ k) ↑ ≈ R^ k • Ex
  lemma-Ex-R^↑ k = begin
    Ex • (R ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) R)) ⟩
    Ex • (R ↑) ^ toℕ k       ≈⟨ lemma-Ex-pow lemma-Ex-R↑ (toℕ k) ⟩
    R ^ toℕ k • Ex ∎

  lemma-Ex-M↑ : ∀ (x' : ℤ* ₚ) → Ex • M x' ↑ ≈ M x' • Ex
  lemma-Ex-M↑ x' =
    lemma-Ex-• (lemma-Ex-R^↑ x)
      (lemma-Ex-• lemma-Ex-H↑
        (lemma-Ex-• (lemma-Ex-R^↑ x⁻¹)
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• (lemma-Ex-R^↑ x) lemma-Ex-H↑))))
    where
    x   = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁)

  lemma-Ex-Mg↑ : Ex • Mg ↑ ≈ Mg • Ex
  lemma-Ex-Mg↑ = lemma-Ex-M↑ g′

  lemma-conj-Ex-Mg↑ : Ex • Mg ↑ • Ex ≈ Mg
  lemma-conj-Ex-Mg↑ = begin
    Ex • Mg ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • Mg ↑) • Ex ≈⟨ cleft lemma-Ex-Mg↑ ⟩
    (Mg • Ex) • Ex   ≈⟨ assoc ⟩
    Mg • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    Mg ∎

  ------------------------------------------------------------------------
  -- The ↓-rules, obtained by conjugating the ↑-rules
  --
  -- This is what the new comm-Ex-CZ axiom buys.  Each proof is the same
  -- three moves: replace the lower-wire word by its Ex-conjugate, push
  -- the CZ through both copies of Ex, and apply the ↑-rule in the middle.

  lemma-comm-CZ-S : CZ • S ≈ S • CZ
  lemma-comm-CZ-S = begin
    CZ • S                ≈⟨ cright sym lemma-conj-Ex-S↑ ⟩
    CZ • (Ex • S ↑ • Ex)  ≈⟨ by-assoc auto ⟩
    (CZ • Ex) • S ↑ • Ex  ≈⟨ cleft sym lemma-Ex-CZ ⟩
    (Ex • CZ) • S ↑ • Ex  ≈⟨ by-assoc auto ⟩
    Ex • (CZ • S ↑) • Ex  ≈⟨ cright cleft axiom comm-CZ-S↑ ⟩
    Ex • (S ↑ • CZ) • Ex  ≈⟨ by-assoc auto ⟩
    (Ex • S ↑) • CZ • Ex  ≈⟨ cright sym lemma-Ex-CZ ⟩
    (Ex • S ↑) • Ex • CZ  ≈⟨ by-assoc auto ⟩
    (Ex • S ↑ • Ex) • CZ  ≈⟨ cleft lemma-conj-Ex-S↑ ⟩
    S • CZ ∎

  -- Every re-bracketing here is an explicit assoc rather than by-assoc:
  -- the tactic compares to-list, and to-list is stuck on CZ^ g = CZ ^ toℕ g,
  -- whose exponent is symbolic.
  lemma-semi-Mg-CZ : Mg • CZ ≈ CZ^ g • Mg
  lemma-semi-Mg-CZ = begin
    Mg • CZ                       ≈⟨ cleft sym lemma-conj-Ex-Mg↑ ⟩
    (Ex • (Mg ↑ • Ex)) • CZ       ≈⟨ assoc ⟩
    Ex • ((Mg ↑ • Ex) • CZ)       ≈⟨ cright assoc ⟩
    Ex • (Mg ↑ • (Ex • CZ))       ≈⟨ cright cright lemma-Ex-CZ ⟩
    Ex • (Mg ↑ • (CZ • Ex))       ≈⟨ cright sym assoc ⟩
    Ex • ((Mg ↑ • CZ) • Ex)       ≈⟨ cright cleft axiom semi-M↑CZ ⟩
    Ex • ((CZ^ g • Mg ↑) • Ex)    ≈⟨ cright assoc ⟩
    Ex • (CZ^ g • (Mg ↑ • Ex))    ≈⟨ sym assoc ⟩
    (Ex • CZ^ g) • (Mg ↑ • Ex)    ≈⟨ cleft lemma-Ex-CZᵏ (toℕ g) ⟩
    (CZ^ g • Ex) • (Mg ↑ • Ex)    ≈⟨ assoc ⟩
    CZ^ g • (Ex • (Mg ↑ • Ex))    ≈⟨ cright lemma-conj-Ex-Mg↑ ⟩
    CZ^ g • Mg ∎

------------------------------------------------------------------------
-- The shift down is the identity on the one-wire words
--
-- _↓ maps every gate to itself, so it is definitionally the identity on
-- a word built from gate letters — but it is stuck on a power with a
-- symbolic exponent, which is what these propositional equations step
-- over.  They are needed because Simplified-V1 states semi-M↓CZ over
-- Mg ↓ rather than Mg.

module Down-Identity where

  lemma-S⁻¹↓ : (S⁻¹ {n}) ↓ ≡ S⁻¹
  lemma-S⁻¹↓ = lemma-↓^ p-1 S

  lemma-Z↓ : (Z {n}) ↓ ≡ Z
  lemma-Z↓ = Eq.cong (λ w → H • H • S • H • H • w) lemma-S⁻¹↓

  lemma-Z^↓ : ∀ k → (Z^ k {n}) ↓ ≡ Z^ k
  lemma-Z^↓ k =
    Eq.trans (lemma-↓^ (toℕ k) Z) (Eq.cong (_^ toℕ k) lemma-Z↓)

  lemma-R↓ : (R {n}) ↓ ≡ R
  lemma-R↓ = Eq.cong (S •_) (lemma-Z^↓ 1/2)

  lemma-R^↓ : ∀ k → (R^ {n} k) ↓ ≡ R^ k
  lemma-R^↓ k =
    Eq.trans (lemma-↓^ (toℕ k) R) (Eq.cong (_^ toℕ k) lemma-R↓)

  lemma-M↓ : ∀ (x' : ℤ* ₚ) → (M {n} x') ↓ ≡ M x'
  lemma-M↓ x' = Eq.cong₂ (λ a b → a • H • b • H • a • H)
                         (lemma-R^↓ x) (lemma-R^↓ x⁻¹)
    where
    x   = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁)

  lemma-Mg↓ : (Mg {n}) ↓ ≡ Mg
  lemma-Mg↓ = lemma-M↓ g′

------------------------------------------------------------------------
-- The two Simplified-V1 axioms that Paper-V0 lacked
--
-- Both are now consequences of comm-Ex-CZ: the ↑-rule conjugated by the
-- swap, with the ↓ on the outside stepped over by Down-Identity.

module Down-Rules (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Ex-Conjugation n
  open Down-Identity

  lemma-comm-CZ-S↓ : CZ • S ↓ ≈ S ↓ • CZ
  lemma-comm-CZ-S↓ = lemma-comm-CZ-S

  lemma-semi-M↓CZ : Mg ↓ • CZ ≈ CZ^ g • Mg ↓
  lemma-semi-M↓CZ = begin
    Mg ↓ • CZ     ≈⟨ refl' (Eq.cong (_• CZ) lemma-Mg↓) ⟩
    Mg • CZ       ≈⟨ lemma-semi-Mg-CZ ⟩
    CZ^ g • Mg    ≈⟨ refl' (Eq.cong (CZ^ g •_) (Eq.sym lemma-Mg↓)) ⟩
    CZ^ g • Mg ↓ ∎

------------------------------------------------------------------------
-- The remote CZ, at three wires
--
-- CZ02 is *defined* as Ex • CZ ↑ • Ex — the CZ on wires 1-2 carried onto
-- wires 0-2 by the swap of wires 0-1 — so conjugation facts about it are
-- definitional, and its order follows from the order of CZ.
--
-- This is the correction term of the paper's C18
-- (semi-CX↑-CZ↓ : CX ↑ • CZ ↓ === CZ ↓ • CZ02 • CX ↑): CX ↑ retargets
-- wire 1, which is what a CZ on wires 0-1 reads, so pushing that CZ
-- through picks up a CZ on wires 0-2.  Deriving selinger-c12 turns on
-- those corrections cancelling, and they cancel because CX ↑ occurs in
-- the C6-expansion of a CZ with total exponent 1 + (p-1) = p, leaving
-- CZ02 ^ p ≈ ε.

module Three-Wire (n : ℕ) where

  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Ex-Conjugation (₁₊ n)

  -- The relation one wire down, for the arguments of lemma-cong↑.
  private module PB₂ = PB ((₂₊ n) QRel,_===_)

  -- CZ on the upper pair has order p, inherited from order-CZ one wire
  -- down.  (ε ↑ is ε definitionally, so the shift leaves no residue.)
  lemma-order-CZ↑ : (CZ ↑) ^ p ≈ ε
  lemma-order-CZ↑ = begin
    (CZ ↑) ^ p  ≈⟨ refl' (Eq.sym (lemma-↑^ p CZ)) ⟩
    (CZ ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (PB₂.axiom order-CZ) ⟩
    ε ∎

  -- Conjugation commutes with powers.  Stated over an arbitrary u so it
  -- serves CZ02 and anything else conjugated by the swap.
  lemma-conj-pow : ∀ (u : Word (Gen (₃₊ n))) k →
                   (Ex • (u • Ex)) ^ k ≈ Ex • (u ^ k • Ex)
  lemma-conj-pow u ₀ = begin
    ε              ≈⟨ sym lemma-Ex-Ex ⟩
    Ex • Ex        ≈⟨ cright sym left-unit ⟩
    Ex • (ε • Ex) ∎
  lemma-conj-pow u ₁ = refl
  lemma-conj-pow u (₂₊ k) = begin
    (Ex • (u • Ex)) • (Ex • (u • Ex)) ^ ₁₊ k
      ≈⟨ cright lemma-conj-pow u (₁₊ k) ⟩
    (Ex • (u • Ex)) • (Ex • (u ^ ₁₊ k • Ex))
      ≈⟨ assoc ⟩
    Ex • ((u • Ex) • (Ex • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright assoc ⟩
    Ex • (u • (Ex • (Ex • (u ^ ₁₊ k • Ex))))
      ≈⟨ cright cright sym assoc ⟩
    Ex • (u • ((Ex • Ex) • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright cright cleft lemma-Ex-Ex ⟩
    Ex • (u • (ε • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright cright left-unit ⟩
    Ex • (u • (u ^ ₁₊ k • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((u • u ^ ₁₊ k) • Ex) ∎

  -- The remote CZ has order p as well: p copies of it are p copies of
  -- CZ ↑ with the two swaps cancelling.
  lemma-order-CZ02 : CZ02 ^ p ≈ ε
  lemma-order-CZ02 = begin
    CZ02 ^ p                ≈⟨ lemma-conj-pow (CZ ↑) p ⟩
    Ex • ((CZ ↑) ^ p • Ex)  ≈⟨ cright cleft lemma-order-CZ↑ ⟩
    Ex • (ε • Ex)           ≈⟨ cright left-unit ⟩
    Ex • Ex                 ≈⟨ lemma-Ex-Ex ⟩
    ε ∎
