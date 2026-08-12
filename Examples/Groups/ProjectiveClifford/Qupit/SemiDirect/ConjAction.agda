------------------------------------------------------------------------
-- Presentations of groups
--
-- The conjugation action is well defined.
--
-- SDProduct gives conj only on generators; the semidirect product needs
-- it to respect both factors' rules once extended to words.  Rather
-- than checking each rule by hand, everything goes through the
-- semantics: conjugating a Pauli word by a symplectic word computes the
-- symplectic action on the Pauli vector,
--
--   sem ((conj ʰ') c w) ≡ ap ⟦ c ⟧ (sem w)          (conjw-sem)
--
-- which needs only the fourteen generator cases of conj.  Both
-- obligations then follow from soundness and completeness of the two
-- presentations, which are theorems already:
--
--   * a Pauli rule has equal readings, so the conjugates do too, so
--     they are equal in the Pauli presentation (respects-Γ);
--   * a symplectic rule has equal denotations, hence equal actions, so
--     again the conjugates have equal readings (respects-Δ).
--
-- In particular the long symplectic rules — M-power, semi-M↑CZ,
-- semi-M↓CZ, selinger-c10 … c15 — are never conjugated by hand.
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

module Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.ConjAction
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0#)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʰ' ; _ⁿ')
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; pI ; pIₙ ; _+₁_ ; _+ₚ_ ; +ₚ-identityˡ)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; _≈ˢ_ ; _∘ˢ_ ; module Interpretation)
open Symplectic using (ap ; linear-+)
open Interpretation using (⟦_⟧ᵍ ; ⟦_⟧)
-- mult and mult-p moved to ForStdlib.Data.Fin.Mod.Prime.Properties in 33ff400; Presentation-Alt
-- only imports them, so they have to come from there directly.
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime using (mult ; mult-p)
open import Examples.Groups.ProjectivePauli.Presentation-Alt p-2 p-prime as XZ
  using (sem ; ⟦_⟧₀ ; sem-↑ ; sem-X^ ; sound-ax ; module Build)
import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen as SimPres
open import Examples.Construct.SemiDirectProduct.Clifford p-2 p-prime using (ap-ε)
open import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Syntactics p-3 p-prime g* g-gen
  using (module SemiDirect)

open NSim.Symplectic using (Gen ; H-gen ; S-gen ; CZ-gen ; _↥)
open SemiDirect using (conj)

------------------------------------------------------------------------
-- Two arithmetic facts

-- The action fixes the zero Pauli.
actg-pI : ∀ {n} (c : Gen n) → ap ⟦ c ⟧ᵍ (pIₙ {n}) ≡ pIₙ
actg-pI c = ap-ε ⟦ c ⟧ᵍ

-- p-1 ones make -1: from ₁ + mult p-1 ≡ mult p ≡ ₀.
mult-p-1 : mult p-1 ≡ - ₁
mult-p-1 = begin
  mult p-1                  ≡⟨ Eq.sym (+-identityˡ (mult p-1)) ⟩
  ₀ + mult p-1              ≡⟨ Eq.cong (_+ mult p-1) (Eq.sym (+-inverseˡ ₁)) ⟩
  ((- ₁) + ₁) + mult p-1    ≡⟨ +-assoc (- ₁) ₁ (mult p-1) ⟩
  (- ₁) + (₁ + mult p-1)    ≡⟨ Eq.cong ((- ₁) +_) mult-p ⟩
  (- ₁) + ₀                 ≡⟨ +-identityʳ (- ₁) ⟩
  - ₁                       ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The bridge, on generators
--
-- Conjugating a Pauli generator by a symplectic generator computes the
-- symplectic action on the corresponding one-hot Pauli vector.

conj-gen : ∀ {n} (c : Gen n) (x : XZ.Gen n) →
           sem (conj c x) ≡ ap ⟦ c ⟧ᵍ ⟦ x ⟧₀
-- H sends X to Z and Z to X⁻¹.
conj-gen {₁₊ n} H-gen XZ.X-gen =
  Eq.cong (λ z → (z , ₁) ∷ pIₙ) (Eq.sym -0#≈0#)
conj-gen {₁₊ n} H-gen XZ.Z-gen =
  Eq.trans (sem-X^ p-1) (Eq.cong (λ z → (z , ₀) ∷ pIₙ) mult-p-1)
-- S sends X to XZ and fixes Z.
conj-gen {₁₊ n} S-gen XZ.X-gen =
  Eq.cong₂ _∷_ (Eq.cong (_, (₀ + ₁)) (+-identityʳ ₁)) (+ₚ-identityˡ pIₙ)
conj-gen {₁₊ n} S-gen XZ.Z-gen =
  Eq.cong (λ z → (₀ , z) ∷ pIₙ) (Eq.sym (+-identityʳ ₁))
-- CZ couples the two wires' X's into the other's Z.
conj-gen {₂₊ n} CZ-gen XZ.X-gen =
  Eq.cong₂ _∷_ (Eq.cong (_, (₀ + ₀)) (+-identityʳ ₁))
    (Eq.cong₂ _∷_ (Eq.cong (_, (₀ + ₁)) (+-identityʳ ₀)) (+ₚ-identityˡ pIₙ))
conj-gen {₂₊ n} CZ-gen (XZ.X-gen XZ.↥) =
  Eq.cong₂ _∷_ (Eq.cong (_, (₀ + ₁)) (+-identityʳ ₀))
    (Eq.cong₂ _∷_ (Eq.cong (_, (₀ + ₀)) (+-identityʳ ₁)) (+ₚ-identityˡ pIₙ))
conj-gen {₂₊ n} CZ-gen XZ.Z-gen =
  Eq.cong₂ _∷_ (Eq.cong (₀ ,_) (Eq.sym (+-identityʳ ₁)))
    (Eq.cong (λ z → (₀ , z) ∷ pIₙ) (Eq.sym (+-identityʳ ₀)))
conj-gen {₂₊ n} CZ-gen (XZ.Z-gen XZ.↥) =
  Eq.cong₂ _∷_ (Eq.cong (₀ ,_) (Eq.sym (+-identityʳ ₀)))
    (Eq.cong (λ z → (₀ , z) ∷ pIₙ) (Eq.sym (+-identityʳ ₁)))
-- A generator on a higher wire is untouched by the bottom-wire gates.
conj-gen {₂₊ n} H-gen (xz XZ.↥) =
  Eq.cong (λ z → (z , ₀) ∷ ⟦ xz ⟧₀) (Eq.sym -0#≈0#)
conj-gen {₂₊ n} S-gen (xz XZ.↥) =
  Eq.cong (λ z → (₀ , z) ∷ ⟦ xz ⟧₀) (Eq.sym (+-identityʳ ₀))
conj-gen {₃₊ n} CZ-gen (xz XZ.↥ XZ.↥) =
  Eq.cong₂ _∷_ (Eq.cong (₀ ,_) (Eq.sym (+-identityʳ ₀)))
    (Eq.cong (λ z → (₀ , z) ∷ ⟦ xz ⟧₀) (Eq.sym (+-identityʳ ₀)))
-- The three clauses above each leave their lowest width uncovered: a
-- shifted Pauli generator on one wire, or twice-shifted on two, comes
-- from XZ.Gen ₀, which only gate₀ inhabits.  The Pauli gate set has no
-- 0-ary gate, so those cases are vacuous.  (Before Circuit.Base gained
-- gate₀ this was invisible, XZ.Gen ₀ having had no constructor at all.)
conj-gen {₁} H-gen ((XZ.gate₀ ()) XZ.↥)
conj-gen {₁} S-gen ((XZ.gate₀ ()) XZ.↥)
conj-gen {₂} CZ-gen (((XZ.gate₀ ()) XZ.↥) XZ.↥)
-- A gate on a higher wire fixes the bottom wire's generators.
conj-gen {₁₊ n} (c ↥) XZ.X-gen = Eq.cong ((₁ , ₀) ∷_) (Eq.sym (actg-pI c))
conj-gen {₁₊ n} (c ↥) XZ.Z-gen = Eq.cong ((₀ , ₁) ∷_) (Eq.sym (actg-pI c))
conj-gen {₁₊ n} (c ↥) (xz XZ.↥) =
  Eq.trans (sem-↑ (conj c xz)) (Eq.cong (pI ∷_) (conj-gen c xz))

------------------------------------------------------------------------
-- The bridge, on words

-- Conjugating a Pauli word by a symplectic generator.
conj-sem : ∀ {n} (c : Gen n) (w : Word (XZ.Gen n)) →
           sem ((conj ⁿ') c w) ≡ ap ⟦ c ⟧ᵍ (sem w)
conj-sem c [ x ]ʷ  = conj-gen c x
conj-sem c ε       = Eq.sym (actg-pI c)
conj-sem c (u • v) =
  Eq.trans (Eq.cong₂ _+ₚ_ (conj-sem c u) (conj-sem c v))
           (Eq.sym (linear-+ ⟦ c ⟧ᵍ (sem u) (sem v)))

-- Conjugating a Pauli word by a symplectic word.
conjw-sem : ∀ {n} (c : Word (Gen n)) (w : Word (XZ.Gen n)) →
            sem ((conj ʰ') c w) ≡ ap ⟦ c ⟧ (sem w)
conjw-sem [ g ]ʷ  w = conj-sem g w
conjw-sem ε       w = Eq.refl
conjw-sem (c • d) w =
  Eq.trans (conjw-sem c ((conj ʰ') d w))
           (Eq.cong (ap ⟦ c ⟧) (conjw-sem d w))

------------------------------------------------------------------------
-- The two obligations

private
  module _ (n : ℕ) where
    open Build n public using (complete)

-- The action respects the Pauli rules in its acted-on argument: equal
-- readings go in, equal readings come out, and the Pauli presentation
-- is complete.
respects-Γ : ∀ {n} (c : Gen n) {u v : Word (XZ.Gen n)} →
             (n XZ.QRel, u === v) →
             PB._≈_ (XZ._QRel,_===_ n) ((conj ⁿ') c u) ((conj ⁿ') c v)
respects-Γ {n} c {u} {v} ax = complete n
  (Eq.trans (conj-sem c u)
    (Eq.trans (Eq.cong (ap ⟦ c ⟧ᵍ) (sound-ax ax))
              (Eq.sym (conj-sem c v))))

-- The action respects the symplectic rules in its acting argument: a
-- rule's two sides denote the same symplectic transformation, so they
-- act alike.
private
  -- The simplified presentation's own interpretation is the extension
  -- of ⟦_⟧ᵍ built by StarInterp; Interpretation.⟦_⟧ is the same
  -- extension written out, so the two agree.
  module SimP {n : ℕ} = _IsPresentationOf_ (SimPres.presentation {n})

  denote-agrees : ∀ {n} (c : Word (Gen n)) → SimP.⟦ c ⟧ ≡ ⟦ c ⟧
  denote-agrees [ g ]ʷ  = Eq.refl
  denote-agrees ε       = Eq.refl
  denote-agrees (c • d) = Eq.cong₂ _∘ˢ_ (denote-agrees c) (denote-agrees d)

  module SIso {n : ℕ} = GroupMorphisms.IsGroupIsomorphism
                          (_IsPresentationOf_.iso (SimPres.presentation {n}))

  -- Soundness of the simplified presentation: the two sides of a rule
  -- denote the same symplectic transformation, so they act alike.
  denote-eq : ∀ {n} {c d : Word (Gen n)} →
              NSim.Simplified-Relations._QRel,_===_ n c d →
              ap ⟦ c ⟧ ≗ ap ⟦ d ⟧
  denote-eq {n} {c} {d} ax x = begin
    ap ⟦ c ⟧ x       ≡⟨ Eq.cong (λ S → ap S x) (Eq.sym (denote-agrees c)) ⟩
    ap SimP.⟦ c ⟧ x  ≡⟨ SIso.⟦⟧-cong (PB.axiom ax) x ⟩
    ap SimP.⟦ d ⟧ x  ≡⟨ Eq.cong (λ S → ap S x) (denote-agrees d) ⟩
    ap ⟦ d ⟧ x       ∎
    where open Eq.≡-Reasoning

respects-Δ : ∀ {n} {c d : Word (Gen n)} (u : Word (XZ.Gen n)) →
             NSim.Simplified-Relations._QRel,_===_ n c d →
             PB._≈_ (XZ._QRel,_===_ n) ((conj ʰ') c u) ((conj ʰ') d u)
respects-Δ {n} {c} {d} u ax = complete n
  (Eq.trans (conjw-sem c u)
    (Eq.trans (denote-eq ax (sem u)) (Eq.sym (conjw-sem d u))))
