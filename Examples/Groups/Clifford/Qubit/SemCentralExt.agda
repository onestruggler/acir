------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the qubit Clifford group as a CENTRAL extension of
-- PRESENTED groups:
--
--     1 ─→ K ─→ K ×_c Q ─→ Q ─→ 1,
--
-- where both sides are groups of words modulo a congruence:
--
--   * K = the cyclic group of order 8, presented by
--     Examples.Groups.Cyclic.Syntactics — words over a single generator
--     T modulo T⁸ = ε.  It is abelian because its alphabet is a
--     singleton, so `gen-comm` is refl, which is what CocycleGen's
--     word-comm needs of a kernel;
--   * Q = the group presented by Figure8-Mod-Scalar — words over the
--     symplectic gates modulo the mod-scalar rule set.  This is Qubit.
--     SemFE's Q on the nose: both are `•-ε-group` of the same relation
--     and the same Grouplike witness.
--
-- φ, the action of Q on K, is TRIVIAL: ω commutes with every Figure-8
-- circuit (comm₀ of the circuit framework, via Figure8.ω^-central), so
-- the extension is central and a factor set is just a 2-cocycle.  That
-- is `ω-central` below; it is a fact about Figure 8, not a convention,
-- and it is what makes K ×_c Q the right model of the scalar layer
-- rather than merely a group.
--
-- γᶜ, the cocycle, is derived HERE, through Presentation.Construct.
-- Properties.CocycleGen, rather than projected out of Qubit.SemFE's
-- finished factor set — which is why this file depends on neither SemFE
-- nor anything the exact layer proves.  CocycleGen asks only for the
-- correction that a single gate carries against a word,
--
--     G : Gen n → Circuit n → Word ⊤,
--
-- and extends it along the first argument by the cocycle identity
-- itself.  So of Cocycle's four fields, two are free for ANY G at all —
-- the identity and the left normalisation, both of which SemFE proved by
-- hand out of ω-faithfulness — one needs only that G is congruent and
-- normalised, and just one, c-cong, reaches the relators.  That is the
-- whole point of coming this way.
--
-- The generator data itself is the record `GeneratorData`: G together
-- with
--
--   G-cong   G a descends to Q;
--   G-ε      G a ε ≈ ε;
--   f-axiom  each relator of the mod-scalar rule set carries the same
--            correction on either side.
--
-- It is a record rather than an interaction hole so that this file
-- depends on nothing the exact layer proves, and every consequence is
-- stated against a named hypothesis.  It is DISCHARGED, at every width,
-- in Qubit.SemGeneratorData (`generator-data`), which also gives the
-- cocycle, the group and the extension with no hypothesis left; so what
-- is a parameter here is a theorem one file away.
--
-- How that file fills it, since the obvious route does not work.  SemFE
-- has the defect already, and G a v ought to be
-- T ^ toℕ (SemFE.f (section n) [ a ]ʷ v).  Writing that DEFINITION here
-- typechecks nowhere: `_^_` recurses on its exponent, so reducing G a v
-- to weak head normal form forces toℕ of the defect, which forces
-- SemFE's `defect`, the section, the bijective normal form and the whole
-- of ScalarKernel; and conversion reduces both sides to whnf before
-- comparing, so every check that so much as mentions G a v detonates
-- (measured: OOM under a 12 GB cap).  What works is to keep the factor
-- set a module PARAMETER, prove everything against its four laws — where
-- each term mentioning it is neutral and nothing can unfold — and apply
-- it once, at a result type that mentions no cocycle.  That is the same
-- discipline the three generic lemmas at the foot of this file use, and
-- it needs no computing defect, so the mod-17 model is not called on
-- after all.
--
-- NOT CocycleGen.Pairs, which would narrow G to a map on pairs of gates:
-- extending letterwise makes each `pair-word a` a homomorphism Q → K, so
-- it factors through the abelianisation of Q — and C2 and C3 force
-- 2h = 4s = 0 there, so 3(s+h) is never odd and ω would be forced to ε
-- (the argument in Qubit.ExactExtension's header, for why no abelian
-- invariant can see ω).  The scalar cocycle has to sit in the general G.
--
-- What this file adds beyond the cocycle.  The three results below are
-- stated for an ARBITRARY cocycle over arbitrary A and H, and hold of γᶜ
-- by instantiation.  That is not fastidiousness about generality: stated
-- at a concrete cocycle they do not typecheck, for the same reason G
-- does not — the terms compared mention c applied to arguments,
-- conversion stops being syntactic, and the cocycle is normalised.  With
-- the cocycle a variable, nothing can unfold and each proof is a few
-- lines.
--
--   * incl-central — the image of the kernel really is central in the
--     total group.  ForStdlib's CentralExtension says so in its header
--     and builds the group accordingly, but never proves it; the proof
--     is two normalisations and commutativity of the kernel, and it
--     belongs upstream rather than here;
--
--   * same-∙ and same-⁻¹ — the central extension and the twisted product
--     over the same cocycle carry the very same multiplication and the
--     same inverse, by `refl`.  This is the claim FactorSetExtension's
--     header makes ("a trivial action gives exactly the multiplication
--     of the central extension"), checked rather than asserted.  The
--     inverse is where the two look different on paper: the twisted
--     product's is act (x⁻¹) ((a · f x x⁻¹)⁻¹), and the action is what
--     disappears.
--
-- The contrast that gives the file its point: with c ≡ ε the same
-- construction returns the DIRECT product K × Q (Direct-group), the
-- split extension in which a word's scalar can be read off the word.  It
-- needs no generator data, the trivial cocycle carrying none.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.SemCentralExt where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (tt)
open import Level using (Level ; 0ℓ ; _⊔_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
open import Presentation.Construct.Properties.CocycleGen
  using (module Generator-Data)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action)
import ForStdlib.Algebra.Construct.CentralExtension as CE
open CE using (Cocycle)
import ForStdlib.Algebra.Construct.FactorSetExtension as FSE

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; Circuit)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar
  p-2 p-prime as MS
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.GroupLike
  using (grouplike-MS)

-- Only for ω-central, the fact that makes the action trivial.
import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8 using (ω ; _≈ᶠ_ ; ω^-central)

-- The kernel's presentation: ⟨ T ∣ T⁸ ⟩.
import Examples.Groups.Cyclic.Syntactics as Cy
open Cy using (T ; _Cn,_===_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Why the action is trivial
--
-- ω commutes with every Figure-8 circuit, so the scalars are central and
-- the quotient — which would act on them by conjugation — acts trivially.
-- Stated here because the choice of φ below is otherwise a convention.

ω-central : (k : ℕ) (w : F8.Circuit n) → ((ω ^ k) • w) ≈ᶠ (w • (ω ^ k))
ω-central = ω^-central

------------------------------------------------------------------------
-- The two presentations
--
-- The cyclic alphabet is a singleton, so any two of its generators are
-- the same one and commutativity of K is refl.

ΓK : WRel Cy.X
ΓK = 8 Cn,_===_

private
  gen-comm : ∀ (x y : Cy.X) →
             PB._≈_ ΓK ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ)
  gen-comm tt tt = PB.refl

-- Both presented groups, and the machinery that turns generator-level
-- data into a factor set, come from CocycleGen.  Public: the field types
-- of GeneratorData below mention CGn.f, so a client supplying the record
-- has to be able to name it.
module CGn (m : ℕ) =
  Generator-Data ΓK (m MS.CRel,_===_) (Cy.grouplike 7) (grouplike-MS {m})
                 gen-comm

module KB = PB ΓK

-- K: the cyclic group of order 8, as words over T.
K : (n : ℕ) → AbelianGroup 0ℓ 0ℓ
K n = CGn.K n

-- Q: the mod-scalar rule set, as words over the gates.
Q : (n : ℕ) → Group 0ℓ 0ℓ
Q n = CGn.Q n

------------------------------------------------------------------------
-- φ: the action of Q on the scalars, trivial by ω-central

φ : (n : ℕ) → Action (AbelianGroup.rawMonoid (K n)) (Group.rawMonoid (Q n))
φ n = FSE.trivialAction (K n) (Q n)

------------------------------------------------------------------------
-- The hole: the generator data
--
-- The correction one gate carries against a word, and the three
-- conditions CocycleGen asks of it.  Everything below is stated against
-- this record rather than an interaction hole, so that the file rests on
-- nothing the exact layer proves and the hypothesis is visible in every
-- type that depends on it.  Qubit.SemGeneratorData supplies the record
-- at every width, out of SemFE's factor set; see the header for why that
-- has to happen there and not here.

record GeneratorData (n : ℕ) : Set where
  field
    -- The scalar by which the lifts of a and of v fail to compose.
    G       : Gen n → Circuit n → Word Cy.X
    -- It descends to Q …
    G-cong  : (a : Gen n) {v v' : Circuit n} →
              PB._≈_ (n MS.CRel,_===_) v v' → KB._≈_ (G a v) (G a v')
    -- … and it is normalised.
    G-ε     : (a : Gen n) → KB._≈_ (G a ε) ε
    -- Each relator carries the same correction on either side.
    f-axiom : {u u' : Circuit n} → (n MS.CRel,_===_) u u' →
              (v : Circuit n) →
              KB._≈_ (CGn.f n (φ n) G u v) (CGn.f n (φ n) G u' v)

------------------------------------------------------------------------
-- γᶜ: the 2-cocycle
--
-- Assembled from CocycleGen's own lemmas rather than from the FactorSet
-- it packages them into, since a central extension wants a Cocycle.  The
-- two records have the same four fields: with the action trivial,
-- IsNormalisedCocycle's identity
--
--     f x y ∙ f (x·y) z ≈ act x (f y z) ∙ f x (y·z)
--
-- has `act x` the identity by definition, which is Cocycle's identity
-- verbatim.  Note how little of the data each field costs: f-cocycle and
-- f-εˡ take G alone, f-εʳ takes G-cong and G-ε, and only f-cong reaches
-- the relators.

γᶜ : (n : ℕ) → GeneratorData n → Cocycle (K n) (Q n)
γᶜ n gd = record
  { c         = CGn.f         n (φ n) G
  ; c-cong    = CGn.f-cong    n (φ n) G G-cong G-ε f-axiom
  ; c-εˡ      = CGn.f-εˡ      n (φ n) G
  ; c-εʳ      = CGn.f-εʳ      n (φ n) G G-cong G-ε
  ; cocycle   = CGn.f-cocycle n (φ n) G
  }
  where open GeneratorData gd

------------------------------------------------------------------------
-- The central extension

-- The total group: pairs (scalar , circuit mod scalars), multiplied with
-- the cocycle correction.
Central-group : (n : ℕ) → GeneratorData n → Group 0ℓ 0ℓ
Central-group n gd = CE.group (K n) (Q n) (γᶜ n gd)

Central-extension : (n : ℕ) (gd : GeneratorData n) →
                    Extension (AbelianGroup.group (K n)) (Q n)
Central-extension n gd = CE.centralExtension (K n) (Q n) (γᶜ n gd)

------------------------------------------------------------------------
-- What the construction gives, for any cocycle
--
-- Centrality of the kernel, and agreement with the twisted product.
-- Generic for the reason given in the header: at a concrete cocycle
-- these do not typecheck, because comparing terms that mention c forces
-- the cocycle to be normalised.  Each holds of γᶜ by instantiating A, H
-- and γ'.

module _ {a b ℓ₁ ℓ₂ : Level} (A : AbelianGroup a ℓ₁) (H : Group b ℓ₂)
         (γ' : Cocycle A H) where

  private
    module A′ = AbelianGroup A
    module H′ = Group H
    module C′ = Cocycle γ'
    module G′ = Group (CE.group A H γ')

    -- The twisted product over the same cocycle, with the action trivial.
    Twisted′ : Group (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
    Twisted′ = FSE.group A H (FSE.trivialAction A H) (FSE.fromCocycle A H γ')

  -- The inclusion of the kernel, taken from the extension itself.
  incl : A′.Carrier → A′.Carrier × H′.Carrier
  incl = Extension.incl (CE.centralExtension A H γ')

  ----------------------------------------------------------------------
  -- The image of the kernel is central
  --
  -- incl a is (a , ε), so both products leave the cocycle applied to a
  -- unit, where it vanishes; what is left is commutativity of A in the
  -- first component and the two unit laws of H in the second.  This is
  -- the property the construction is named for, and the one a semidirect
  -- product cannot have unless it is a direct product.

  incl-central : (a₁ : A′.Carrier) (u : A′.Carrier × H′.Carrier) →
                 (incl a₁ G′.∙ u) G′.≈ (u G′.∙ incl a₁)
  incl-central a₁ (b , y) = first , second
    where
    first : ((a₁ A′.∙ b) A′.∙ C′.c H′.ε y)
              A′.≈ ((b A′.∙ a₁) A′.∙ C′.c y H′.ε)
    first =
      A′.trans (A′.∙-congˡ (C′.c-εˡ y))
        (A′.trans (A′.identityʳ (a₁ A′.∙ b))
          (A′.trans (A′.comm a₁ b)
            (A′.trans (A′.sym (A′.identityʳ (b A′.∙ a₁)))
                      (A′.∙-congˡ (A′.sym (C′.c-εʳ y))))))

    second : (H′.ε H′.∙ y) H′.≈ (y H′.∙ H′.ε)
    second = H′.trans (H′.identityˡ y) (H′.sym (H′.identityʳ y))

  ----------------------------------------------------------------------
  -- The same group as the twisted product
  --
  -- Not merely isomorphic: the same carrier, the same multiplication and
  -- the same inverse, definitionally.  Both check by `refl` once the
  -- pairs are exposed, since _∙′_ and _⁻¹′ are defined by matching.

  same-∙ : (u v : A′.Carrier × H′.Carrier) →
           Group._∙_ (CE.group A H γ') u v ≡ Group._∙_ Twisted′ u v
  same-∙ (a₁ , x) (a₂ , y) = Eq.refl

  same-⁻¹ : (u : A′.Carrier × H′.Carrier) →
            Group._⁻¹ (CE.group A H γ') u ≡ Group._⁻¹ Twisted′ u
  same-⁻¹ (a₁ , x) = Eq.refl

------------------------------------------------------------------------
-- The three at the scalar layer
--
-- Applying a generic lemma at γᶜ costs nothing — an application never
-- has to look inside the cocycle — so these are the concrete statements,
-- obtained the only way they can be.  Their types are left to be
-- inferred: writing one out would name c at arguments, which is the
-- thing that does not check.

incl-central-ms = λ (n : ℕ) (gd : GeneratorData n) →
                  incl-central (K n) (Q n) (γᶜ n gd)

same-∙-ms       = λ (n : ℕ) (gd : GeneratorData n) →
                  same-∙ (K n) (Q n) (γᶜ n gd)

same-⁻¹-ms      = λ (n : ℕ) (gd : GeneratorData n) →
                  same-⁻¹ (K n) (Q n) (γᶜ n gd)

------------------------------------------------------------------------
-- The split instance
--
-- c ≡ ε is a cocycle, and the extension it names is the DIRECT product
-- K × Q: the one in which the scalar of a product is the sum of the
-- scalars, i.e. in which w ↦ (ε , w) is a homomorphic section.  It needs
-- no generator data, the trivial cocycle carrying none.

γᶜ-split : (n : ℕ) → Cocycle (K n) (Q n)
γᶜ-split n = CE.trivialCocycle (K n) (Q n)

Direct-group : (n : ℕ) → Group 0ℓ 0ℓ
Direct-group n = CE.group (K n) (Q n) (γᶜ-split n)

Direct-extension : (n : ℕ) → Extension (AbelianGroup.group (K n)) (Q n)
Direct-extension n = CE.centralExtension (K n) (Q n) (γᶜ-split n)
