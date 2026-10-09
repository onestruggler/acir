------------------------------------------------------------------------
-- Presentations of groups
--
-- First consequences of the relations of Table 1: every generator is
-- an involution (1a)–(1c), so words have inverses and cancel, and an
-- equation A g ≈ g B can be read the other way round.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.CCX+HH-TwoLevel.Derived {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Product.Base using (_,_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

------------------------------------------------------------------------
-- Involutions and inverses

-- Every generator is an involution.
gen-gen : (g : Gen n) → [ g ]ʷ • [ g ]ʷ ≈ ε
gen-gen (M-gen a)             = axiom r1b
gen-gen (X-gen a b p)         = axiom (r1a p)
gen-gen (K-gen a b c d p q r) = axiom (r1c p q r)

grouplike : Grouplike (_===_ {n})
grouplike g = [ g ]ʷ , gen-gen g

open Group-Lemmas (_===_ {n}) grouplike public
  using (_⁻¹ ; inverseˡ ; inverseʳ ; •-cancelˡ ; •-cancelʳ ; ⁻¹-cong)

------------------------------------------------------------------------
-- Conjugation by a generator

-- A g ≈ g B gives B g ≈ g A.
flip : ∀ {A B : Word (Gen n)} (g : Gen n) → A • [ g ]ʷ ≈ [ g ]ʷ • B → B • [ g ]ʷ ≈ [ g ]ʷ • A
flip {A = A} {B} g h = begin
  B • G                         ≈⟨ sym left-unit ⟩
  ε • (B • G)                   ≈⟨ cleft sym (gen-gen g) ⟩
  (G • G) • (B • G)             ≈⟨ assoc ⟩
  G • (G • (B • G))             ≈⟨ cright sym assoc ⟩
  G • ((G • B) • G)             ≈⟨ cright cleft sym h ⟩
  G • ((A • G) • G)             ≈⟨ cright assoc ⟩
  G • (A • (G • G))             ≈⟨ cright cright gen-gen g ⟩
  G • (A • ε)                   ≈⟨ cright right-unit ⟩
  G • A                         ∎
  where G = [ g ]ʷ

-- g A ≈ B g gives A ≈ g B g.
conj : ∀ {A B : Word (Gen n)} (g : Gen n) → [ g ]ʷ • A ≈ B • [ g ]ʷ → A ≈ [ g ]ʷ • (B • [ g ]ʷ)
conj {A = A} {B} g h = begin
  A                             ≈⟨ sym left-unit ⟩
  ε • A                         ≈⟨ cleft sym (gen-gen g) ⟩
  (G • G) • A                   ≈⟨ assoc ⟩
  G • (G • A)                   ≈⟨ cright h ⟩
  G • (B • G)                   ∎
  where G = [ g ]ʷ

-- g A ≈ B g gives B ≈ g A g.
conj′ : ∀ {A B : Word (Gen n)} (g : Gen n) → [ g ]ʷ • A ≈ B • [ g ]ʷ → B ≈ [ g ]ʷ • (A • [ g ]ʷ)
conj′ {A = A} {B} g h = begin
  B                             ≈⟨ sym right-unit ⟩
  B • ε                         ≈⟨ cright sym (gen-gen g) ⟩
  B • (G • G)                   ≈⟨ sym assoc ⟩
  (B • G) • G                   ≈⟨ cleft sym h ⟩
  (G • A) • G                   ≈⟨ assoc ⟩
  G • (A • G)                   ∎
  where G = [ g ]ʷ
