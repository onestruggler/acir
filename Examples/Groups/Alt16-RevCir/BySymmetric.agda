------------------------------------------------------------------------
-- Presentations of groups
--
-- The Reidemeister–Schreier step from Symmetric's presentation of the
-- permutations of N points to the rules (1)–(7) on k wires
--
-- Below four wires the circuits over X, CX, CCX and Ex are all the
-- permutations of the states, and Examples.Groups.Symmetric presents
-- those by the transpositions of two consecutive points, with the
-- Coxeter relations.  This module is the step from that presentation
-- to the rules of Theory at a width k with N states, generic in k: the
-- same step as Iso's from Lafont's presentation, laid out in the same
-- way.
--
-- The translations.  g reads the transposition of the points d, d + 1
-- as a circuit Θ d, and f reads a gate as a word in the transpositions.
--
-- The two relation sets.  Towards the circuits the step asks for the
-- Coxeter relations between the Θ d (order, braid, far) and for each
-- gate to be the circuit of its word (gate): derivations from the
-- rules, which Width2 and Width3 supply.  Towards the transpositions it
-- is semantic, as in Iso: the rules are sound for functions on states,
-- a word in the transpositions permutes the positions as its circuit
-- maps the states (f-sem-gen, g-sem-gen), and Symmetric's presentation
-- is complete.
--
-- The result is that (f ʷ) is an isomorphism of the presented groups,
-- hence that the rules present the permutations of the N states and
-- are complete for functions on the states of k wires.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.BySymmetric where

open import Algebra.Bundles using (Group)
import Algebra.Morphism.Construct.Composition as Compose
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; suc ; _+_ ; _≤_)
open import Data.Nat.Properties
  using (+-suc ; ≤-refl ; ≤-trans ; ≤-reflexive ; n≤1+n ; m+n≤o⇒m≤o)
open import Data.Product using (∃ ; _×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.Embedding using (module Pres)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Presentation.Morphism as Morphism

import Examples.Groups.Symmetric.Completeness as SC
import Examples.Groups.Symmetric.Interpretation as SI
import Examples.Groups.Symmetric.Presentation as SP
open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Alt16-RevCir.Semantics
  using (Bits ; ⟦_⟧ᵍ ; ⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics using (Gen ; Circuit)
open import Examples.Groups.Alt16-RevCir.Theory using (module T ; T-sound)

open GroupMorphisms using (IsGroupIsomorphism)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- The transpositions as circuits

-- The generator y, d points further up, as a circuit: Θ of where its
-- transposition sits.
gᵈ : (ℕ → Circuit k) → ℕ → S.Gen n → Circuit k
gᵈ Θ d S.σ-gen   = Θ d
gᵈ Θ d (y S.↥)   = gᵈ Θ (suc d) y

-- A word one point up, read d points up, is the word read d + 1 points
-- up.
gᵈ-↑ : (Θ : ℕ → Circuit k) (d : ℕ) (w : S.Circuit n) →
       (gᵈ Θ d ʷ) (w S.↑) ≡ (gᵈ Θ (suc d) ʷ) w
gᵈ-↑ Θ d [ y ]ʷ  = Eq.refl
gᵈ-↑ Θ d ε       = Eq.refl
gᵈ-↑ Θ d (w • v) = Eq.cong₂ _•_ (gᵈ-↑ Θ d w) (gᵈ-↑ Θ d v)

-- One point carries no transposition.
no-gen₁ : S.Gen 1 → ⊥
no-gen₁ (S.gate₀ ())
no-gen₁ (S.gate₁ ())
no-gen₁ (S.gate₀ () S.↥)

------------------------------------------------------------------------
-- The step

module Step
  {k N : ℕ}
  -- the translations
  (Θ : ℕ → Circuit k)
  (f : Gen k → S.Circuit N)
  -- the numbering of the states
  (enc : Fin N → Bits k) (dec : Bits k → Fin N)
  (dec-enc : ∀ i → dec (enc i) ≡ i) (enc-dec : ∀ x → enc (dec x) ≡ x)
  -- the Coxeter relations between the Θ d, from the rules
  (order : ∀ d → 2 + d ≤ N → k T.⊢ Θ d • Θ d ≈ ε)
  (braid : ∀ d → 3 + d ≤ N →
           k T.⊢ Θ d • Θ (suc d) • Θ d ≈ Θ (suc d) • Θ d • Θ (suc d))
  (far   : ∀ d e → 2 + d ≤ e → 2 + e ≤ N → k T.⊢ Θ e • Θ d ≈ Θ d • Θ e)
  -- each gate is the circuit of its word, from the rules
  (gate  : (x : Gen k) → k T.⊢ [ x ]ʷ ≈ (gᵈ Θ 0 ʷ) (f x))
  -- the semantics of the translations
  (f-sem-gen : (x : Gen k) (i : Fin N) →
               SI.⟦ f x ⟧ ⟨$⟩ʳ i ≡ dec (⟦ x ⟧ᵍ (enc i)))
  (g-sem-gen : (y : S.Gen N) (i : Fin N) →
               dec (⟦ gᵈ Θ 0 y ⟧ (enc i)) ≡ SI.⟦ [ y ]ʷ ⟧ ⟨$⟩ʳ i)
  where

  g : S.Gen N → Circuit k
  g = gᵈ Θ 0

  private
    -- Symmetric's presentation; its words are a group by its gl.
    module SPres = _IsPresentationOf_ (SP.presentation {N})

    infix 4 _≈₁_ _≈₂_
    _≈₁_ : Circuit k → Circuit k → Set
    _≈₁_ = PB._≈_ (T._VRel,_===_ k)

    _≈₂_ : S.Circuit N → S.Circuit N → Set
    _≈₂_ = PB._≈_ (S._VRel,_===_ N)

  ----------------------------------------------------------------------
  -- A word in the transpositions and the function of a circuit

  f-sem : (w : Circuit k) (i : Fin N) →
          SI.⟦ (f ʷ) w ⟧ ⟨$⟩ʳ i ≡ dec (⟦ w ⟧ (enc i))
  f-sem [ x ]ʷ  i = f-sem-gen x i
  f-sem ε       i = Eq.sym (dec-enc i)
  f-sem (w • v) i =
    Eq.trans (Eq.cong (SI.⟦ (f ʷ) v ⟧ ⟨$⟩ʳ_) (f-sem w i))
    (Eq.trans (f-sem v (dec (⟦ w ⟧ (enc i))))
              (Eq.cong (λ s → dec (⟦ v ⟧ s)) (enc-dec (⟦ w ⟧ (enc i)))))

  ----------------------------------------------------------------------
  -- Symmetric's relations, read through g

  private
    -- The same N points, counted from one point further up.
    up : ∀ d {m} → d + suc m ≡ N → suc d + m ≡ N
    up d {m} = Eq.trans (Eq.sym (+-suc d m))

    up₂ : ∀ d {m} → d + (2 + m) ≡ N → 2 + d + m ≡ N
    up₂ d eq = up (suc d) (up d eq)

    -- A transposition d points up, with m points above it, fits.
    fits₂ : ∀ d {m} → d + (2 + m) ≡ N → 2 + d ≤ N
    fits₂ d eq = m+n≤o⇒m≤o (2 + d) (≤-reflexive (up₂ d eq))

    fits₃ : ∀ d {m} → d + (3 + m) ≡ N → 3 + d ≤ N
    fits₃ d eq =
      m+n≤o⇒m≤o (3 + d) (≤-reflexive (up (2 + d) (up₂ d eq)))

    -- The circuits Θ j with c ≤ j.
    Above : ℕ → Circuit k → Set
    Above c w = ∃ λ j → w ≡ Θ j × c ≤ j × 2 + j ≤ N

    -- A generator read c points up is one of them.
    gᵈ-above : ∀ {m} (c : ℕ) (y : S.Gen m) → c + m ≡ N →
               Above c (gᵈ Θ c y)
    gᵈ-above c S.σ-gen eq = c , Eq.refl , ≤-refl , fits₂ c eq
    gᵈ-above c (y S.↥) eq =
      let (j , e , c<j , j-fits) = gᵈ-above (suc c) y (up c eq)
      in j , e , ≤-trans (n≤1+n c) c<j , j-fits

    -- Θ d commutes with the transpositions two or more points up.
    lemma-far : ∀ d {w} → Above (2 + d) w → w • Θ d ≈₁ Θ d • w
    lemma-far d (j , Eq.refl , d+2≤j , j-fits) = far d j d+2≤j j-fits

  lemma-g-rel : ∀ {n} (d : ℕ) → d + n ≡ N → {u t : S.Circuit n} →
                S._VRel,_===_ n u t → (gᵈ Θ d ʷ) u ≈₁ (gᵈ Θ d ʷ) t
  lemma-g-rel d eq (S.srel S.order)       = order d (fits₂ d eq)
  lemma-g-rel d eq (S.srel S.yang-baxter) = braid d (fits₃ d eq)
  lemma-g-rel d eq (S.cong↑ {w = w} {v = v} p) =
    PB.trans (refl' (gᵈ-↑ Θ d w))
    (PB.trans (lemma-g-rel (suc d) (up d eq) p)
              (refl' (Eq.sym (gᵈ-↑ Θ d v))))
    where open PB (T._VRel,_===_ k) using (refl')
  lemma-g-rel d eq (S.comm₂ S.σ-gate y) =
    lemma-far d (gᵈ-above (2 + d) y (up₂ d eq))

  ----------------------------------------------------------------------
  -- The isomorphism

  module Theorem where

    -- f : circuits → words in the transpositions.  A rule equates two
    -- circuits with the same function on states, so their words have
    -- the same permutation, and are equal by completeness.
    f-well-defined : ∀ {w v} → T._VRel,_===_ k w v →
                     (f ʷ) w ≈₂ (f ʷ) v
    f-well-defined {w} {v} r =
      SC.completeness {N} {(f ʷ) w} {(f ʷ) v} λ i →
        Eq.trans (f-sem w i)
        (Eq.trans (Eq.cong dec (T-sound (PB.axiom r) (enc i)))
                  (Eq.sym (f-sem v i)))

    -- g : words in the transpositions → circuits.  Each instance of a
    -- Coxeter relation is one between the Θ d.
    g-well-defined : ∀ {u t} → S._VRel,_===_ N u t →
                     (g ʷ) u ≈₁ (g ʷ) t
    g-well-defined = lemma-g-rel 0 Eq.refl

    -- A transposition and the word of its circuit have the same
    -- permutation.
    f-left-inv-gen : (y : S.Gen N) → [ y ]ʷ ≈₂ (f ʷ) (g y)
    f-left-inv-gen y =
      SC.completeness {N} {[ y ]ʷ} {(f ʷ) (g y)} λ i →
        Eq.trans (Eq.sym (g-sem-gen y i)) (Eq.sym (f-sem (g y) i))

    g-left-inv-gen : (x : Gen k) → [ x ]ʷ ≈₁ (g ʷ) (f x)
    g-left-inv-gen = gate

    -- Group-likeness, transported: the inverse of a gate x is the
    -- circuit of the inverse, in Symmetric's word group, of the word
    -- of x.
    open Morphism (S._VRel,_===_ N) (T._VRel,_===_ k)
      using (module Star-Congruence)
    open Star-Congruence g g-well-defined
      using () renaming (fʷ-cong to gʷ-cong)

    grouplike : Grouplike (T._VRel,_===_ k)
    grouplike x =
      (g ʷ) (f x SPres.GL.⁻¹) ,
      PB.trans (PB.cong PB.refl (g-left-inv-gen x))
               (gʷ-cong (SPres.GL.inverseˡ {f x}))

    private
      module G₁ = Group-Lemmas (T._VRel,_===_ k) grouplike

    open Morphism (T._VRel,_===_ k) (S._VRel,_===_ N)
      using (module GroupMorphism)
    open GroupMorphism grouplike SPres.gl
      using (module StarGroupIsomorphism)

    Theorem-Circuits-iso-Transpositions :
      IsGroupIsomorphism (Group.rawGroup G₁.•-ε-group)
                         (Group.rawGroup SPres.GL.•-ε-group) (f ʷ)
    Theorem-Circuits-iso-Transpositions =
      StarGroupIsomorphism.isGroupIsomorphism
        f g f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen

  open Theorem public

  ----------------------------------------------------------------------
  -- The presentation, and completeness for functions on states

  private
    module G₁ = Group-Lemmas (T._VRel,_===_ k) grouplike

  -- The isomorphism, followed by Symmetric's.
  presentation : (T._VRel,_===_ k) IsPresentationOf (Permutation′-group N)
  presentation = record
    { gl  = grouplike
    ; ⟦_⟧ = λ w → SI.⟦ (f ʷ) w ⟧
    ; iso = Compose.isGroupIsomorphism
              {G₁ = Group.rawGroup G₁.•-ε-group}
              {G₂ = Group.rawGroup SPres.GL.•-ε-group}
              {G₃ = Group.rawGroup (Permutation′-group N)}
              (λ {x} {y} {z} →
                 Group.trans (Permutation′-group N) {x} {y} {z})
              {f = f ʷ} {g = SPres.⟦_⟧}
              Theorem-Circuits-iso-Transpositions SPres.iso
    }

  -- Two circuits with the same function on states are equal by the
  -- rules.
  complete : ∀ {w v : Circuit k} → ⟦ w ⟧ ≐ ⟦ v ⟧ → k T.⊢ w ≈ v
  complete {w} {v} e = Pres.complete presentation {w} {v} λ i →
    Eq.trans (f-sem w i)
    (Eq.trans (Eq.cong dec (e (enc i))) (Eq.sym (f-sem v i)))
