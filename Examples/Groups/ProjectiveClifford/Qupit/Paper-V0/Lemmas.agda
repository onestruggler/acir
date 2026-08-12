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
