------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary A.7
--
-- Two circuits with one Hadamard pair between Hadamard-free halves,
-- each half invertible by the other, that denote the same operator are
-- equivalent.  The paper's argument in three lines: B′A commutes with
-- the pair semantically, so by Lemma A.6 it crosses it, and then
--
--     A hh A′  ≈  (BB′) A hh A′  ≈  B (Λ B′A) A′  ≈  B hh B′ (AA′)
--
-- is associativity and the two cancellations.  Where the paper then
-- spells out Lemma A.6's normal form and moves it across letter by
-- letter with (38), `Passes` has already done that once and for all.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.A7 (m : ℕ) where

open import Data.Nat renaming (_+_ to _+ℕ_) using ()
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; nil ; cat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; idSP ; ⊙-inverse ; sp-inj)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (spOp ; spOp-⊙ ; spOp-id ; spOp-cong ; spOp-inj
       ; word-op ; word-scale ; ⟦_⟧ʷ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m
  using (Passes ; Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A6 m
  using (Mpair ; A6 ; Λ-op ; Λ-scale ; ~≡)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  n : ℕ
  n = ₃₊ m

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- Reading the hypotheses

-- A Hadamard-free word and its inverse, as signed permutations.
inverse-sp : ∀ {u v : W} → HFreeʷ u → HFreeʷ v → ⟦ u • v ⟧ʷ ~ ⟦ ε ⟧ʷ →
             sp u ⊛ sp v ≗ idSP
inverse-sp {u} {v} hu hv h =
  spOp-inj (≐-trans (≐-sym (word-op (cat hu hv)))
           (≐-trans (~≡ 0 (word-scale (cat hu hv)) Eq.refl h) (≐-sym spOp-id)))

private
  -- Those two facts, as matrices, in both orders.  The words are
  -- explicit: `sp u ⊛ sp v` computes to a record literal, in which a
  -- metavariable would never be solved.
  op-inv : ∀ (u v : W) → sp u ⊛ sp v ≗ idSP →
           (spOp (sp u) ⊙ spOp (sp v)) ≐ Idₒ
  op-inv u v e =
    ≐-trans (≐-sym (spOp-⊙ (sp u) (sp v))) (≐-trans (spOp-cong e) spOp-id)

  op-inv′ : ∀ (u v : W) → sp u ⊛ sp v ≗ idSP →
            (spOp (sp v) ⊙ spOp (sp u)) ≐ Idₒ
  op-inv′ u v e = op-inv v u (⊙-inverse (sp u) (sp v) (sp-inj v) e)

------------------------------------------------------------------------
-- The algebra behind the corollary
--
-- Stated over five abstract operators: with the matrices themselves in
-- the statement the conversion checker would expand every `⊙` into its
-- sum over bitstrings, and a five-fold product is far too much of
-- that.

comm-lemma : ∀ (a a′ b b′ M : Op n) →
             (a′ ⊙ a) ≐ Idₒ → (b′ ⊙ b) ≐ Idₒ →
             (a ⊙ (M ⊙ a′)) ≐ (b ⊙ (M ⊙ b′)) →
             ((b′ ⊙ a) ⊙ M) ≐ (M ⊙ (b′ ⊙ a))
comm-lemma a a′ b b′ M ia ib e =
  ≐-trans (⊙-assoc b′ a M)
  (≐-trans (⊙-cong (≐-refl b′)
             (⊙-cong (≐-refl a)
               (≐-trans (≐-sym (⊙-identityʳ M))
                        (⊙-cong (≐-refl M) (≐-sym ia)))))
  (≐-trans (⊙-cong (≐-refl b′)
             (≐-trans (⊙-cong (≐-refl a) (≐-sym (⊙-assoc M a′ a)))
               (≐-trans (≐-sym (⊙-assoc a (M ⊙ a′) a))
                        (⊙-cong e (≐-refl a)))))
  (≐-trans (⊙-cong (≐-refl b′)
             (≐-trans (⊙-assoc b (M ⊙ b′) a)
                      (⊙-cong (≐-refl b) (⊙-assoc M b′ a))))
  (≐-trans (≐-sym (⊙-assoc b′ b (M ⊙ (b′ ⊙ a))))
  (≐-trans (⊙-cong ib (≐-refl (M ⊙ (b′ ⊙ a))))
           (⊙-identityˡ (M ⊙ (b′ ⊙ a))))))))

------------------------------------------------------------------------
-- Corollary A.7

A7 : ∀ {A A′ B B′ : W} → HFreeʷ A → HFreeʷ A′ → HFreeʷ B → HFreeʷ B′ →
     ⟦ A • A′ ⟧ʷ ~ ⟦ ε ⟧ʷ → ⟦ B • B′ ⟧ʷ ~ ⟦ ε ⟧ʷ →
     ⟦ A • (Λ • A′) ⟧ʷ ~ ⟦ B • (Λ • B′) ⟧ʷ →
     A • (Λ • A′) ≈ B • (Λ • B′)
A7 {A} {A′} {B} {B′} hA hA′ hB hB′ eA eB eq = begin
  A • (Λ • A′)                  ≈⟨ trans (sym left-unit) (front _ (sym eBB′)) ⟩
  (B • B′) • (A • (Λ • A′))     ≈⟨ shift₁ ⟩
  B • (((B′ • A) • Λ) • A′)     ≈⟨ back B (front A′ pass) ⟩
  B • ((Λ • (B′ • A)) • A′)     ≈⟨ shift₂ ⟩
  B • (Λ • (B′ • (A • A′)))     ≈⟨ back B (back Λ (back B′ eAA′)) ⟩
  B • (Λ • (B′ • ε))            ≈⟨ back B (back Λ right-unit) ⟩
  B • (Λ • B′)                  ∎
  where
  -- The two halves are inverse to one another.
  sA : sp A ⊛ sp A′ ≗ idSP
  sA = inverse-sp hA hA′ eA

  sB : sp B ⊛ sp B′ ≗ idSP
  sB = inverse-sp hB hB′ eB

  eAA′ : A • A′ ≈ ε
  eAA′ = A5-full (cat hA hA′) nil sA

  eBB′ : B • B′ ≈ ε
  eBB′ = A5-full (cat hB hB′) nil sB

  -- The matrices in play.
  a a′ b b′ : Op n
  a  = spOp (sp A)
  a′ = spOp (sp A′)
  b  = spOp (sp B)
  b′ = spOp (sp B′)

  -- The two circuits denote the same operator, the pair's scale
  -- being the only one on either side.
  scale : ∀ {u v : W} → HFreeʷ u → HFreeʷ v → proj₁ ⟦ u • (Λ • v) ⟧ʷ ≡ 2
  scale hu hv = Eq.cong₂ _+ℕ_ (word-scale hu)
                              (Eq.cong₂ _+ℕ_ Λ-scale (word-scale hv))

  read : ∀ {u v : W} → HFreeʷ u → HFreeʷ v →
         proj₂ ⟦ u • (Λ • v) ⟧ʷ ≐ (spOp (sp u) ⊙ (Mpair ⊙ spOp (sp v)))
  read hu hv = ⊙-cong (word-op hu) (⊙-cong Λ-op (word-op hv))

  Eop : (a ⊙ (Mpair ⊙ a′)) ≐ (b ⊙ (Mpair ⊙ b′))
  Eop = ≐-trans (≐-sym (read hA hA′))
                (≐-trans (~≡ 2 (scale hA hA′) (scale hB hB′) eq) (read hB hB′))

  -- So B′A commutes with the pair.
  comm : ((b′ ⊙ a) ⊙ Mpair) ≐ (Mpair ⊙ (b′ ⊙ a))
  comm = comm-lemma a a′ b b′ Mpair (op-inv′ A A′ sA) (op-inv′ B B′ sB) Eop

  pass : (B′ • A) • Λ ≈ Λ • (B′ • A)
  pass = A6 (cat hB′ hA)
    (≐-trans (⊙-cong (spOp-⊙ (sp B′) (sp A)) (≐-refl Mpair))
    (≐-trans comm
             (⊙-cong (≐-refl Mpair) (≐-sym (spOp-⊙ (sp B′) (sp A))))))

  -- `by-assoc` cannot help here: its flattening does not compute on
  -- word variables, so the re-bracketing is done by hand.
  shift₁ : (B • B′) • (A • (Λ • A′)) ≈ B • (((B′ • A) • Λ) • A′)
  shift₁ = trans assoc (trans (back B (sym assoc)) (back B (sym assoc)))

  shift₂ : B • ((Λ • (B′ • A)) • A′) ≈ B • (Λ • (B′ • (A • A′)))
  shift₂ = back B (trans assoc (back Λ assoc))
