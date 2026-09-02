{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- Group-likeness of the Paper-V1 rules, and powers modulo p.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ< ; toℕ-injective)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
open Lemmas-Clifford
  using (lemma-↑^ ; lemma-Induction ; lemma-Inductionˡ
        ; lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-Hᵏ-w↑
        ; lemma-comm-Z-w↑ ; lemma-comm-X-w↑ ; lemma-comm-CZ-w↑)

private
  variable
    n : ℕ

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire p-3 p-prime g* g-gen

------------------------------------------------------------------------
-- Group-likeness
--
-- Every generator has a left inverse, from the three order axioms.  The
-- same construction as Simplified-V1.Lemmas.Clifford-GroupLike, and for
-- the same reason: the axioms it uses are shared.  Iso.agda gets its
-- witness by transporting V1's along g-well-defined, which is fine there
-- but unusable here — the chains below need right-cancellation, and
-- deriving it from the transported witness would be circular.

module Paper-GroupLike where

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} H-gen = H ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : H ^ 3 • H ≈ ε
    claim = begin
      H ^ 3 • H ≈⟨ by-assoc auto ⟩
      H ^ 4     ≈⟨ One-Wire.lemma-order-H n ⟩
      ε ∎
  grouplike {₁₊ n} S-gen = S ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S       ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p             ≈⟨ axiom order-S ⟩
      ε ∎
  grouplike {₂₊ n} CZ-gen = CZ ^ p-1 , claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    claim : CZ ^ p-1 • CZ ≈ ε
    claim = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ p              ≈⟨ axiom order-CZ ⟩
      ε ∎
  -- Width ₁₊ n rather than ₂₊ n: gate₀ makes Gen 0 inhabited, so a shift
  -- can appear on one wire too.  The witness is width-generic.
  grouplike {₁₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf

------------------------------------------------------------------------
-- Powers of a word of order p depend only on the exponent mod p
--
-- Stated at an arbitrary width, since the multiplier rescalings produce
-- natural-number exponents at both two and three wires.

lemma-pow-mod : ∀ {n} {w : Word (Gen n)} →
                let open PB (n QRel,_===_) using (_≈_) in
                w ^ p ≈ ε → ∀ m → w ^ m ≈ w ^ (m Nat.% p)
lemma-pow-mod {n} {w} op m = begin
  w ^ m
    ≡⟨ Eq.cong (w ^_) (m≡m%n+[m/n]*n m p) ⟩
  w ^ (m Nat.% p Nat.+ (m Nat./ p) Nat.* p)
    ≈⟨ ^-+ w (m Nat.% p) ((m Nat./ p) Nat.* p) ⟩
  w ^ (m Nat.% p) • w ^ ((m Nat./ p) Nat.* p)
    ≈⟨ cright aux ⟩
  w ^ (m Nat.% p) • ε
    ≈⟨ right-unit ⟩
  w ^ (m Nat.% p) ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid
  aux : w ^ ((m Nat./ p) Nat.* p) ≈ ε
  aux = begin
    w ^ ((m Nat./ p) Nat.* p)  ≈⟨ refl' (Eq.cong (w ^_) (NP.*-comm (m Nat./ p) p)) ⟩
    w ^ (p Nat.* (m Nat./ p))  ≈⟨ sym (^^ w p (m Nat./ p)) ⟩
    (w ^ p) ^ (m Nat./ p)      ≈⟨ ^-cong (w ^ p) ε (m Nat./ p) op ⟩
    ε ^ (m Nat./ p)            ≈⟨ ε^k=ε (m Nat./ p) ⟩
    ε ∎

