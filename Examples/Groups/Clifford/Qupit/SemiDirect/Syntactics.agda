------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli-by-symplectic semidirect product, syntactically.
--
-- Generators are XZ.Gen n ⊎ Sym.Gen n: a Pauli on the left, a
-- symplectic gate on the right.  The relation is
--
--   XZ n ⋄ Simplified n ⋄ ConjRelʷ conj
--
-- — the Pauli rules on the left, the simplified symplectic rules on the
-- right, and in the middle the conjugation rule h·n = (conj h n)·h,
-- where conj says how each symplectic generator conjugates each Pauli
-- generator (H swaps X and Z, S sends X to XZ, CZ couples the wires).
--
-- Alongside the relation: the derived words (X, Z, S, H, CZ, M, Ex, …),
-- the embedding lemmas relating [_]ₗ / [_]ᵣ to the wire shift, the
-- congruence lemma-cong↑, and Semi-GroupLike, which gives every
-- generator a left inverse.  This is the same shape as
-- Symplectic.Syntactics, one level up.
--
-- The action's well-definedness is in ConjAction, and the presentation
-- theorem it feeds is in Presentation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
open import Relation.Binary.PropositionalEquality using (_≡_)
-- PrimeModulus' — the modulus interface used in the telescope below —
-- is the one from Fermats-little-theorem.
open import Zp.Fermats-little-theorem using (module PrimeModulus')
open import Zp.ModularArithmetic

module Examples.Groups.Clifford.Qupit.SemiDirect.Syntactics
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Product using (proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike using (Grouplike)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

import Examples.Groups.Pauli.Presentation-Alt p-2 p-prime as XZ
import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
-- Lemmas1 / Lemmas1b / Symplectic-Sim-GroupLike moved here when
-- Simplified.Syntactics was split up.
import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen as NSimL

module Sym = NSim.Symplectic
module Sim = NSim.Simplified-Relations

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Powers commute with the left and right embeddings
--
-- These two lemmas used to live in Presentation.Construct.Properties,
-- which was pruned as dead code once this development stopped being
-- reachable; they are needed only here and in Iso, so they are kept
-- local.

lemma-[w^n]ₗ=[w]ₗ^n : ∀ {A B : Set} (w : Word A) (n : ℕ) →
                      [_]ₗ {B = B} (w ^ n) ≡ [ w ]ₗ ^ n
lemma-[w^n]ₗ=[w]ₗ^n w ₀      = Eq.refl
lemma-[w^n]ₗ=[w]ₗ^n w (₁₊ ₀) = Eq.refl
lemma-[w^n]ₗ=[w]ₗ^n w (₂₊ n) = Eq.cong₂ _•_ Eq.refl (lemma-[w^n]ₗ=[w]ₗ^n w (₁₊ n))

lemma-[w^n]ᵣ=[w]ᵣ^n : ∀ {A B : Set} (w : Word B) (n : ℕ) →
                      [_]ᵣ {A = A} (w ^ n) ≡ [ w ]ᵣ ^ n
lemma-[w^n]ᵣ=[w]ᵣ^n w ₀      = Eq.refl
lemma-[w^n]ᵣ=[w]ᵣ^n w (₁₊ ₀) = Eq.refl
lemma-[w^n]ᵣ=[w]ᵣ^n w (₂₊ n) = Eq.cong₂ _•_ Eq.refl (lemma-[w^n]ᵣ=[w]ᵣ^n w (₁₊ n))


------------------------------------------------------------------------
-- The presentation

module SemiDirect where

  ----------------------------------------------------------------------
  -- Generators

  Gen : ℕ → Set
  Gen n = XZ.Gen n ⊎ Sym.Gen n

  pattern X-gen  = inj₁ XZ.X-gen
  pattern Z-gen  = inj₁ XZ.Z-gen
  pattern H-gen  = inj₂ Sym.H-gen
  pattern S-gen  = inj₂ Sym.S-gen
  pattern CZ-gen = inj₂ Sym.CZ-gen

  -- The bottom wire is the word itself; _↑ shifts every letter up one
  -- wire, on both sides of the sum.

  _↓ : ∀ {n} → Word (Gen n) → Word (Gen n)
  w ↓ = w

  _↑ : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
  [ inj₁ x ]ʷ ↑ = [ inj₁ (x XZ.↥) ]ʷ
  [ inj₂ y ]ʷ ↑ = [ inj₂ (y Sym.↥) ]ʷ
  ε           ↑ = ε
  (w • w₁)    ↑ = w ↑ • w₁ ↑

  ----------------------------------------------------------------------
  -- Derived words

  X : ∀ {n} → Word (Gen (₁₊ n))
  X = [ X-gen ]ʷ

  Z : ∀ {n} → Word (Gen (₁₊ n))
  Z = [ Z-gen ]ʷ

  S : ∀ {n} → Word (Gen (₁₊ n))
  S = [ S-gen ]ʷ

  S⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  S⁻¹ = S ^ p-1

  H : ∀ {n} → Word (Gen (₁₊ n))
  H = [ H-gen ]ʷ

  HH : ∀ {n} → Word (Gen (₁₊ n))
  HH = H ^ 2

  H⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  H⁻¹ = H ^ 3

  CZ : ∀ {n} → Word (Gen (₂₊ n))
  CZ = [ CZ-gen ]ʷ

  CZ⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  CZ⁻¹ = CZ ^ p-1

  -- The four CX-like gates: a CZ conjugated by an H on one wire.

  CX : ∀ {n} → Word (Gen (₂₊ n))
  CX = H ↓ ^ 3 • CZ • H ↓

  XC : ∀ {n} → Word (Gen (₂₊ n))
  XC = H ↑ ^ 3 • CZ • H ↑

  CX' : ∀ {n} → Word (Gen (₂₊ n))
  CX' = H ↓ • CZ • H ↓ ^ 3

  XC' : ∀ {n} → Word (Gen (₂₊ n))
  XC' = H ↑ • CZ • H ↑ ^ 3

  -- The exchange gate and its two halves.

  ₕ|ₕ : ∀ {n} → Word (Gen (₂₊ n))
  ₕ|ₕ = H ↓ • CZ • H ↓

  ʰ|ʰ : ∀ {n} → Word (Gen (₂₊ n))
  ʰ|ʰ = H ↑ • CZ • H ↑

  ⊥⊤ : ∀ {n} → Word (Gen (₂₊ n))
  ⊥⊤ = ₕ|ₕ • ʰ|ʰ

  ⊤⊥ : ∀ {n} → Word (Gen (₂₊ n))
  ⊤⊥ = ʰ|ʰ • ₕ|ₕ

  Ex : ∀ {n} → Word (Gen (₂₊ n))
  Ex = CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑

  ----------------------------------------------------------------------
  -- Powers indexed by a modular exponent

  H^ : ∀ {n} → ℤ ₄ → Word (Gen (₁₊ n))
  H^ k = H ^ toℕ k

  S^ : ∀ {n} → ℤ ₚ → Word (Gen (₁₊ n))
  S^ k = S ^ toℕ k

  Z^ : ∀ {n} → ℤ ₚ → Word (Gen (₁₊ n))
  Z^ k = Z ^ toℕ k

  CZ^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  CZ^ k = CZ ^ toℕ k

  CX^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  CX^ k = CX ^ toℕ k

  M : ∀ {n} → ℤ* ₚ → Word (Gen (₁₊ n))
  M x' = S^ x • H • S^ x⁻¹ • H • S^ x • H
    where
    x   = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁

  M₁ : ∀ {n} → Word (Gen (₁₊ n))
  M₁ = M ₁ₚ

  CX⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  CX⁻¹ = H ^ 3 • CZ^ (- ₁) • H

  XC⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  XC⁻¹ = H ↑ ^ 3 • CZ^ (- ₁) • H ↑

  CX'^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  CX'^ k = H ^ 3 • CZ^ k • H

  XC^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  XC^ k = XC ^ toℕ k

  XC'^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  XC'^ k = H ↑ ^ 3 • CZ^ k • H ↑

  ----------------------------------------------------------------------
  -- The CZ between wires 0 and 2, reached through the exchange gate

  CZ02 : ∀ {n} → Word (Gen (₃₊ n))
  CZ02 = Ex • CZ ↑ • Ex

  CZ02' : ∀ {n} → Word (Gen (₃₊ n))
  CZ02' = Ex ↑ • CZ • Ex ↑

  CZ02⁻¹ : ∀ {n} → Word (Gen (₃₊ n))
  CZ02⁻¹ = Ex • CZ⁻¹ ↑ • Ex

  CZ02'⁻¹ : ∀ {n} → Word (Gen (₃₊ n))
  CZ02'⁻¹ = Ex ↑ • CZ⁻¹ • Ex ↑

  CZ02k : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02k k = Ex • CZ ↑ ^ k • Ex

  CZ02'k : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02'k k = Ex ↑ • CZ ^ k • Ex ↑

  CZ02⁻ᵏ : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02⁻ᵏ k = Ex • CZ⁻¹ ↑ ^ k • Ex

  CZ02'⁻ᵏ : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02'⁻ᵏ k = Ex ↑ • CZ⁻¹ ^ k • Ex ↑

  CZ02^ : ∀ {n} (k : ℤ ₚ) → Word (Gen (₃₊ n))
  CZ02^ k = Ex • CZ^ k ↑ • Ex

  CZ02'^ : ∀ {n} (k : ℤ ₚ) → Word (Gen (₃₊ n))
  CZ02'^ k = CZ02 ^ toℕ k

  XC02 : ∀ {n} → Word (Gen (₃₊ n))
  XC02 = H ↑ ↑ ^ 3 • CZ02 • H ↑ ↑

  XC02^ : ∀ {n} → ℤ ₚ → Word (Gen (₃₊ n))
  XC02^ k = H ↑ ↑ ^ 3 • CZ02^ k • H ↑ ↑

  CX02^ : ∀ {n} → ℤ ₚ → Word (Gen (₃₊ n))
  CX02^ k = H ^ 3 • CZ02^ k • H

  ----------------------------------------------------------------------
  -- The conjugation action
  --
  -- conj h x is the Pauli word h·x·h⁻¹: H swaps X and Z, S sends X to
  -- X·Z, CZ couples the two bottom wires, and a shifted gate acts on a
  -- shifted Pauli only.

  conj : Sym.Gen n → XZ.Gen n → Word (XZ.Gen n)
  conj Sym.H-gen   XZ.X-gen           = XZ.Z
  conj Sym.H-gen   XZ.Z-gen           = XZ.X ^ p-1
  conj Sym.H-gen   (xz XZ.↥)          = [ xz ]ʷ XZ.↑
  conj Sym.S-gen   XZ.X-gen           = XZ.X • XZ.Z
  conj Sym.S-gen   XZ.Z-gen           = XZ.Z
  conj Sym.S-gen   (xz XZ.↥)          = [ xz ]ʷ XZ.↑
  conj Sym.CZ-gen  XZ.X-gen           = XZ.X • XZ.Z XZ.↑
  conj Sym.CZ-gen  XZ.Z-gen           = XZ.Z
  conj Sym.CZ-gen  (XZ.X-gen XZ.↥)    = XZ.X XZ.↑ • XZ.Z
  conj Sym.CZ-gen  (XZ.Z-gen XZ.↥)    = XZ.Z XZ.↑
  conj Sym.CZ-gen  (xz XZ.↥ XZ.↥)     = [ xz ]ʷ XZ.↑ XZ.↑
  conj (sym Sym.↥) XZ.X-gen           = XZ.X
  conj (sym Sym.↥) XZ.Z-gen           = XZ.Z
  conj (sym Sym.↥) (xz XZ.↥)          = conj sym xz XZ.↑

  ----------------------------------------------------------------------
  -- The relation

  infix 4 _QRel,_===_
  _QRel,_===_ : (n : ℕ) → WRel (Gen n)
  _QRel,_===_ n = XZ._QRel,_===_ n ⋄ Sim._QRel,_===_ n ⋄ ConjRelʷ conj

  -- The axioms of the two sides, under the names they had before the
  -- amalgamation.

  pattern order-X   = left XZ.order-X
  pattern order-Z   = left XZ.order-Z
  pattern comm-Z-X  = left XZ.comm-Z-X
  pattern comm-Z    = left (XZ.comm₁ XZ.Z-gate _)
  pattern comm-X    = left (XZ.comm₁ XZ.X-gate _)

  pattern order-S   = right (Sim.srel Sim.order-S)
  pattern order-H   = right (Sim.srel Sim.order-H)
  pattern M-power   = right (Sim.srel Sim.M-power)
  pattern semi-MS   = right (Sim.srel Sim.semi-MS)

  ----------------------------------------------------------------------
  -- The embeddings and the wire shift
  --
  -- Shifting a word up commutes with either embedding, and both
  -- embeddings are monoid maps, hence commute with powers.

  lemma-[]ₗ-↑ : ∀ (u : Word (XZ.Gen n)) → [ u ]ₗ ↑ ≡ [ u XZ.↑ ]ₗ
  lemma-[]ₗ-↑ [ XZ.X-gen ]ʷ = auto
  lemma-[]ₗ-↑ [ XZ.Z-gen ]ʷ = auto
  lemma-[]ₗ-↑ [ x XZ.↥ ]ʷ   = auto
  lemma-[]ₗ-↑ ε             = auto
  lemma-[]ₗ-↑ (u • v)       = Eq.cong₂ _•_ (lemma-[]ₗ-↑ u) (lemma-[]ₗ-↑ v)

  lemma-[]ᵣ-↑ : ∀ (u : Word (Sym.Gen n)) → [ u ]ᵣ ↑ ≡ [ u Sym.↑ ]ᵣ
  lemma-[]ᵣ-↑ [ Sym.H-gen ]ʷ  = auto
  lemma-[]ᵣ-↑ [ Sym.S-gen ]ʷ  = auto
  lemma-[]ᵣ-↑ [ Sym.CZ-gen ]ʷ = auto
  lemma-[]ᵣ-↑ [ x Sym.↥ ]ʷ    = auto
  lemma-[]ᵣ-↑ ε               = auto
  lemma-[]ᵣ-↑ (u • v)         = Eq.cong₂ _•_ (lemma-[]ᵣ-↑ u) (lemma-[]ᵣ-↑ v)

  lemma-[]ₗ^k : ∀ (u : Word (XZ.Gen n)) k →
                [_]ₗ {B = Sym.Gen n} (u ^ k) ≡ [ u ]ₗ ^ k
  lemma-[]ₗ^k u ₀                  = auto
  lemma-[]ₗ^k u ₁                  = auto
  lemma-[]ₗ^k u (₁₊ k'@(₁₊ k''))   = Eq.cong₂ _•_ auto (lemma-[]ₗ^k u k')

  lemma-[]ᵣ^k : ∀ (u : Word (Sym.Gen n)) k →
                [_]ᵣ {A = XZ.Gen n} (u ^ k) ≡ [ u ]ᵣ ^ k
  lemma-[]ᵣ^k u ₀                  = auto
  lemma-[]ᵣ^k u ₁                  = auto
  lemma-[]ᵣ^k u (₁₊ k'@(₁₊ k''))   = Eq.cong₂ _•_ auto (lemma-[]ᵣ^k u k')

  ----------------------------------------------------------------------
  -- Congruence under the wire shift
  --
  -- Every derivation at width n transports to width 1+n.  The two
  -- interesting clauses are the mid-axioms whose conjugate is not
  -- syntactically a shifted word; they go through lemma-[]ₗ-↑.

  lemma-cong↑ : ∀ {n} w v →
    let
    open PB (n QRel,_===_) using (_≈_)
    open PB ((₁₊ n) QRel,_===_) renaming (_≈_ to _≈↑_) using ()
    in
    w ≈ v → w ↑ ≈↑ v ↑
  lemma-cong↑ w v PB.refl          = PB.refl
  lemma-cong↑ w v (PB.sym eq)      = PB.sym (lemma-cong↑ v w eq)
  lemma-cong↑ w v (PB.trans eq eq₁) =
    PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v (PB.cong eq eq₁)  =
    PB.cong (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v PB.assoc         = PB.assoc
  lemma-cong↑ w v PB.left-unit     = PB.left-unit
  lemma-cong↑ w v PB.right-unit    = PB.right-unit
  lemma-cong↑ {₁₊ n} w v (PB.axiom (left {u} {v₁} x))
    rewrite lemma-[]ₗ-↑ u | lemma-[]ₗ-↑ v₁ = PB.axiom (left (XZ.cong↑ x))
  lemma-cong↑ {₁₊ n} w v (PB.axiom (right {u} {v₁} x))
    rewrite lemma-[]ᵣ-↑ u | lemma-[]ᵣ-↑ v₁ = PB.axiom (right (Sim.cong↑ x))
  -- At width 0 both sides are empty: every base axiom needs at least one
  -- wire, and cong↑/comm₁/comm₂ each produce a successor width.  The XZ
  -- side needs saying now that it too is a Lift-Relation, since the
  -- emptiness is no longer visible in the shape of a datatype.
  lemma-cong↑ {₀} w v (PB.axiom (right (Sim.srel ())))
  lemma-cong↑ {₀} w v (PB.axiom (left (XZ.srel ())))
  lemma-cong↑ w v (PB.axiom (mid (comm XZ.X-gen Sym.H-gen))) =
    PB.axiom (mid (comm (XZ.X-gen XZ.↥) (Sym.H-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm XZ.X-gen Sym.S-gen))) =
    PB.axiom (mid (comm (XZ.X-gen XZ.↥) (Sym.S-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm XZ.X-gen Sym.CZ-gen))) =
    PB.axiom (mid (comm (XZ.X-gen XZ.↥) (Sym.CZ-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm XZ.X-gen (b Sym.↥)))) =
    PB.axiom (mid (comm (XZ.X-gen XZ.↥) ((b Sym.↥) Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.Z-gen Sym.H-gen))) = begin
    H ↑ • Z ↑
      ≈⟨ axiom (mid (comm (XZ.Z-gen XZ.↥) (Sym.H-gen Sym.↥))) ⟩
    ([ conj Sym.H-gen XZ.Z-gen XZ.↑ ]ₗ) • H ↑
      ≡⟨ Eq.sym (Eq.cong (\ xx → xx • H ↑)
                         (lemma-[]ₗ-↑ (conj Sym.H-gen XZ.Z-gen))) ⟩
    ([ conj Sym.H-gen XZ.Z-gen ]ₗ ↑) • H ↑ ∎
    where
    open PB (n QRel,_===_) using (_≈_)
    open PB ((₁₊ n) QRel,_===_) renaming (_≈_ to _≈↑_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
  lemma-cong↑ w v (PB.axiom (mid (comm XZ.Z-gen Sym.S-gen))) =
    PB.axiom (mid (comm (XZ.Z-gen XZ.↥) (Sym.S-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm XZ.Z-gen Sym.CZ-gen))) =
    PB.axiom (mid (comm (XZ.Z-gen XZ.↥) (Sym.CZ-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm XZ.Z-gen (b Sym.↥)))) =
    PB.axiom (mid (comm (XZ.Z-gen XZ.↥) ((b Sym.↥) Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm (a XZ.↥) Sym.H-gen))) =
    PB.axiom (mid (comm ((a XZ.↥) XZ.↥) (Sym.H-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm (a XZ.↥) Sym.S-gen))) =
    PB.axiom (mid (comm ((a XZ.↥) XZ.↥) (Sym.S-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm (XZ.X-gen XZ.↥) Sym.CZ-gen))) =
    PB.axiom (mid (comm ((XZ.X-gen XZ.↥) XZ.↥) (Sym.CZ-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm (XZ.Z-gen XZ.↥) Sym.CZ-gen))) =
    PB.axiom (mid (comm ((XZ.Z-gen XZ.↥) XZ.↥) (Sym.CZ-gen Sym.↥)))
  lemma-cong↑ w v (PB.axiom (mid (comm ((a XZ.↥) XZ.↥) Sym.CZ-gen))) =
    PB.axiom (mid (comm (((a XZ.↥) XZ.↥) XZ.↥) (Sym.CZ-gen Sym.↥)))
  lemma-cong↑ {₁₊ n@(₁₊ n')} w v (PB.axiom (mid (comm (a XZ.↥) (b Sym.↥)))) = begin
    [ inj₂ (b Sym.↥ Sym.↥) ]ʷ • [ inj₁ (a XZ.↥ XZ.↥) ]ʷ
      ≈⟨ refl ⟩
    [ inj₂ (b Sym.↥) ]ʷ ↑ • [ inj₁ (a XZ.↥) ]ʷ ↑
      ≈⟨ PB.axiom (mid (comm ((a XZ.↥) XZ.↥) ((b Sym.↥) Sym.↥))) ⟩
    [ conj b a XZ.↑ XZ.↑ ]ₗ • [ inj₂ (b Sym.↥) ]ʷ ↑
      ≡⟨ Eq.cong (\ xx → xx • [ inj₂ (b Sym.↥) ]ʷ ↑)
                 (Eq.sym (lemma-[]ₗ-↑ (conj b a XZ.↑))) ⟩
    ([ conj b a XZ.↑ ]ₗ ↑) • [ inj₂ (b Sym.↥ Sym.↥) ]ʷ ∎
    where
    open PB ((₁₊ n) QRel,_===_) using (_≈_)
    open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↑_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


------------------------------------------------------------------------
-- Group-likeness
--
-- Every generator has a left inverse: the Pauli ones come from the XZ
-- presentation, the symplectic ones from Simplified, and both transport
-- along the corresponding embedding.

module Semi-GroupLike where

  open SemiDirect

  private
    -- The congruences of the two sides, at a fixed width.
    module LRC (m : ℕ) = LeftRightCongruence
      (XZ._QRel,_===_ m) (Sim._QRel,_===_ m) (ConjRelʷ conj)

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} H-gen = H ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LRC (₁₊ n)
    open NSimL.Lemmas1 n
    claim : H ^ 3 • H ≈ ε
    claim = begin
      H ^ 3 • H       ≈⟨ by-assoc auto ⟩
      [ Sym.H ^ 4 ]ᵣ  ≈⟨ rights lemma-order-H ⟩
      ε ∎

  grouplike {₁₊ n} S-gen = S ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LRC (₁₊ n)
    module RG = NSimL.Symplectic-Sim-GroupLike
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S
        ≡⟨ Eq.cong (\ xx → xx • S) (Eq.sym (lemma-[]ᵣ^k Sym.S p-1)) ⟩
      [ Sym.S ^ p-1 • Sym.S ]ᵣ
        ≈⟨ rights (RG.grouplike Sym.S-gen .proj₂) ⟩
      ε ∎

  grouplike {₂₊ n} CZ-gen = CZ ^ p-1 , claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open LRC (₂₊ n)
    module RG = NSimL.Symplectic-Sim-GroupLike
    claim : CZ ^ p-1 • CZ ≈ ε
    claim = begin
      CZ ^ p-1 • CZ
        ≡⟨ Eq.cong (\ xx → xx • CZ) (Eq.sym (lemma-[]ᵣ^k Sym.CZ p-1)) ⟩
      [ Sym.CZ ^ p-1 • Sym.CZ ]ᵣ
        ≈⟨ rights (RG.grouplike Sym.CZ-gen .proj₂) ⟩
      ε ∎

  grouplike {₁₊ n} X-gen = X ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LRC (₁₊ n)
    module LG = XZ.XZ-GroupLike
    claim : X ^ p-1 • X ≈ ε
    claim = begin
      X ^ p-1 • X
        ≡⟨ Eq.cong (\ xx → xx • X) (Eq.sym (lemma-[]ₗ^k XZ.X p-1)) ⟩
      [ XZ.X ^ p-1 • XZ.X ]ₗ
        ≈⟨ lefts (LG.grouplike XZ.X-gen .proj₂) ⟩
      ε ∎

  grouplike {₁₊ n} Z-gen = Z ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LRC (₁₊ n)
    module LG = XZ.XZ-GroupLike
    claim : Z ^ p-1 • Z ≈ ε
    claim = begin
      Z ^ p-1 • Z
        ≡⟨ Eq.cong (\ xx → xx • Z) (Eq.sym (lemma-[]ₗ^k XZ.Z p-1)) ⟩
      [ XZ.Z ^ p-1 • XZ.Z ]ₗ
        ≈⟨ lefts (LG.grouplike XZ.Z-gen .proj₂) ⟩
      ε ∎

  -- A shifted generator inherits its inverse from one wire down.
  grouplike {₂₊ n} (inj₁ (g XZ.↥)) with XZ.XZ-GroupLike.grouplike (g XZ.↥)
  ... | ig , prf = [ ig ]ₗ , lefts prf
    where open LRC (₂₊ n)
  grouplike {₂₊ n} (inj₂ (g Sym.↥)) with NSimL.Symplectic-Sim-GroupLike.grouplike (g Sym.↥)
  ... | ig , prf = [ ig ]ᵣ , rights prf
    where open LRC (₂₊ n)
