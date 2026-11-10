------------------------------------------------------------------------
-- Presentations of groups
--
-- The normal form of the circuits on four wires over X, CX, CCX and
-- Ex: Lafont's canonical forms of the even permutations of sixteen
-- points, translated
--
-- Lafont's canonical form of an even permutation of n points
-- (Examples.Groups.Alternating.Normalization) is a canonical form on
-- the points 1, …, n - 1 followed by a stairs: a run of cycles ω₀ ω₁ …
-- that brings some point to position 0, its last cycle doubled when it
-- comes from the last point.  Read through the translation g of the
-- cycles into circuits, a stairs at the points from d on is the
-- circuit Ω d • Ω (1 + d) • … (stairs), and a canonical form is the
-- product of its stairs, the highest first (canon).  That circuit is
-- the translation of Lafont's canonical form, letter for letter
-- (canon-g).
--
-- The normal form of a circuit is Lafont's normal form of its word in
-- the cycles (nf).  With Lafont's Lemmas 6 and 8 and the presentation
-- (Presentation) this gives: every circuit is equal by the rules to
-- its canonical circuit (normal-form); nf respects the rules
-- (nf-cong) and fixes the canonical circuits (nf-canon); canonical
-- circuits with the same function are the same (canon-unique); and
-- every even permutation is carried out by one (canon-onto).
--
-- Every statement here is generic: nothing is proved by evaluating a
-- normal form.  Lafont's nf works by rewriting, and on the word of a
-- circuit it passes through millions of letters.  To compute the
-- normal form of a circuit, read it off the circuit's permutation
-- instead: nf-sem says it is the canonical form that Lafont's Lemma 6
-- (Surjectivity.canonical) finds for that permutation, by recursion on
-- the sixteen points.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.NormalForm where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Uniqueness.Propositional as NFU
import Presentation.Base as PB
open import Presentation.Embedding using (module Pres)
open import Word.Base using (ε ; _•_ ; _ʷ)

open import Examples.Groups.Alternating.Cosets
  using (C ; ε ; ω•_ ; ωω ; [_]ᶜ)
open import Examples.Groups.Alternating.Derivations using (fig10)
open import Examples.Groups.Alternating.Interpretation
  using () renaming (⟦_⟧ to L⟦_⟧)
import Examples.Groups.Alternating.Normalization as N
open import Examples.Groups.Alternating.Presentation as LA using ()
open import Examples.Groups.Alternating.Semantics
  using (Alt ; Alt-group ; _≈ᴬ_)
open import Examples.Groups.Alternating.Surjectivity using (canonical)
import Examples.Groups.Alternating.Syntactics as L
open import Examples.Groups.Alternating.UniqueNormalForm
  using (inv-nf-injective)

open import Examples.Groups.Alt16-RevCir.Bridge using (g-sem)
open import Examples.Groups.Alt16-RevCir.Lemmas using (gᵈ-↑)
open import Examples.Groups.Alt16-RevCir.Numbering using (enc ; dec)
open import Examples.Groups.Alt16-RevCir.Presentation
  using (⟦_⟧ᴬ ; ⟦⟧ᴬ-sem ; presentation)
open import Examples.Groups.Alt16-RevCir.Semantics using (⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics
open import Examples.Groups.Alt16-RevCir.Translation using (f ; g ; gᵈ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Canonical circuits

-- Lafont's canonical forms of the even permutations of sixteen points.
NF : Set
NF = N.NF 16

-- A stairs at the points from d on: the cycles Ω d, Ω (1 + d), …, the
-- last one doubled for ωω.
stairs : ℕ → C n → Circuit 4
stairs d ε      = ε
stairs d (ω• c) = Ω d • stairs (suc d) c
stairs d ωω     = Ω d • Ω d

-- A canonical form at the points from d on: the canonical form of the
-- points above d, then the stairs at d.
canonᵈ : ℕ → N.NF n → Circuit 4
canonᵈ {zero}  d tt      = ε
canonᵈ {suc n} d (x , c) = canonᵈ (suc d) x • stairs d c

canon : NF → Circuit 4
canon = canonᵈ 0

-- These are Lafont's stairs and canonical forms, read through g.
stairs-g : (d : ℕ) (c : C n) → stairs d c ≡ (gᵈ d ʷ) [ c ]ᶜ
stairs-g d ε      = refl
stairs-g d (ω• c) =
  cong (Ω d •_) (trans (stairs-g (suc d) c) (sym (gᵈ-↑ d [ c ]ᶜ)))
stairs-g d ωω     = refl

canonᵈ-g : (d : ℕ) (x : N.NF n) → canonᵈ d x ≡ (gᵈ d ʷ) (N.inv-nf x)
canonᵈ-g {zero}  d tt      = refl
canonᵈ-g {suc n} d (x , c) =
  cong₂ _•_ (trans (canonᵈ-g (suc d) x) (sym (gᵈ-↑ d (N.inv-nf x))))
            (stairs-g d c)

canon-g : (x : NF) → canon x ≡ (g ʷ) (N.inv-nf x)
canon-g = canonᵈ-g 0

------------------------------------------------------------------------
-- The normal form of a circuit

-- Lafont's normal form of the circuit's word in the cycles.
nf : Circuit 4 → NF
nf w = N.nf ((f ʷ) w)

private
  -- Lafont's Lemma 8, read in the permutations: a word in the cycles
  -- and its canonical form have the same permutation.
  lemma-8 : (u : L.Circuit n) → L⟦ N.inv-nf (N.nf u) ⟧ ≈ᴬ L⟦ u ⟧
  lemma-8 u = LA.soundness (N.inv-nf∘nf≈id fig10 u)

  -- So the normal form of a word is the canonical form of its
  -- permutation, canonical forms being unique.  The permutation is a
  -- variable: at sixteen points canonical computes, and two spellings
  -- of its argument would be compared through sixteen levels of it.
  nf-semᴸ : (u : L.Circuit n) {a : Alt n} → a ≡ L⟦ u ⟧ →
            N.nf u ≡ proj₁ (canonical n a)
  nf-semᴸ {n} u {a} refl =
    inv-nf-injective {n} {N.nf u} {proj₁ (canonical n a)} λ i →
      trans (lemma-8 u i) (sym (proj₂ (canonical n a) i))

  -- A canonical circuit carries out the permutation of Lafont's
  -- canonical form: it is that form's circuit, and g keeps the meaning.
  canon-sem : (x : NF) → ⟦ canon x ⟧ᴬ ≈ᴬ L⟦ N.inv-nf x ⟧
  canon-sem x i =
    trans (⟦⟧ᴬ-sem (canon x) i)
    (trans (cong (λ w → dec (⟦ w ⟧ (enc i))) (canon-g x))
           (g-sem (N.inv-nf x) i))

  -- Circuits with the same function have the same permutation.
  ≐⇒≈ᴬ : ∀ {w v : Circuit 4} → ⟦ w ⟧ ≐ ⟦ v ⟧ → ⟦ w ⟧ᴬ ≈ᴬ ⟦ v ⟧ᴬ
  ≐⇒≈ᴬ {w} {v} e i =
    trans (⟦⟧ᴬ-sem w i)
          (trans (cong dec (e (enc i))) (sym (⟦⟧ᴬ-sem v i)))

  -- Canonical circuits with the same permutation are the same.
  unique : ∀ {x y : NF} → ⟦ canon x ⟧ᴬ ≈ᴬ ⟦ canon y ⟧ᴬ → x ≡ y
  unique {x} {y} e = inv-nf-injective {16} {x} {y} λ i →
    trans (sym (canon-sem x i)) (trans (e i) (canon-sem y i))

-- The normal form, read off the circuit's permutation.
nf-sem : (w : Circuit 4) → nf w ≡ proj₁ (canonical 16 ⟦ w ⟧ᴬ)
nf-sem w = nf-semᴸ ((f ʷ) w) {⟦ w ⟧ᴬ} refl

------------------------------------------------------------------------
-- The theorems

-- Every circuit is equal by the rules to its canonical circuit: the
-- two have the same permutation.
normal-form : (w : Circuit 4) → 4 ⊢ canon (nf w) ≈ w
normal-form w = Pres.complete presentation {canon (nf w)} {w} λ i →
  trans (canon-sem (nf w) i) (lemma-8 ((f ʷ) w) i)

-- Circuits equal by the rules have the same normal form.
nf-cong : ∀ {w v : Circuit 4} → 4 ⊢ w ≈ v → nf w ≡ nf v
nf-cong {w} {v} e =
  inv-nf-injective {16} {nf w} {nf v} λ i →
    trans (lemma-8 ((f ʷ) w) i)
    (trans (Pres.sound presentation e i)
           (sym (lemma-8 ((f ʷ) v) i)))

-- A canonical circuit is its own normal form.
nf-canon : (x : NF) → nf (canon x) ≡ x
nf-canon x = inv-nf-injective {16} {nf (canon x)} {x} λ i →
  trans (lemma-8 ((f ʷ) (canon x)) i) (canon-sem x i)

-- Canonical circuits with the same function are the same.
canon-unique : ∀ {x y : NF} → ⟦ canon x ⟧ ≐ ⟦ canon y ⟧ → x ≡ y
canon-unique {x} {y} e = unique (≐⇒≈ᴬ {canon x} {canon y} e)

-- Every even permutation of the sixteen positions is carried out by a
-- canonical circuit.
canon-onto : (a : Alt 16) → Σ NF (λ x → ⟦ canon x ⟧ᴬ ≈ᴬ a)
canon-onto a =
  let (x , e) = canonical 16 a
  in x , λ i → trans (canon-sem x i) (e i)

------------------------------------------------------------------------
-- The normal form, packaged

-- nf is a normal form with the canonical circuits as its section,
nfp′ : NFBase.NormalForm (4 VRel,_===_) NF
nfp′ = record
  { rightInverse = record
    { to        = nf
    ; from      = canon
    ; to-cong   = nf-cong
    ; from-cong = λ { refl → PB.refl }
    ; inverseʳ  = λ { refl → normal-form _ }
    }
  }

-- and they are unique for the semantics.
unique-nf : NFU.UniqueNormalForm (4 VRel,_===_) NF
              (Group.setoid (Alt-group 16)) ⟦_⟧ᴬ canon
unique-nf = record { unique = unique }
