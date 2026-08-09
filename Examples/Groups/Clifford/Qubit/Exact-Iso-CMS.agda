------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figure 8 against the exact extension presentation.
--
-- Two rule sets describe the same group, the n-qubit Clifford group with
-- its order-8 scalar:
--
--   1) _CRel,_===_ of Qubit.Selinger.Figure8, over ExactGate — the
--      scalar ω is a 0-ary generator alongside H, S and CZ;
--   2) _Exact,_===_ (Qubit.Exact-Presentation), over ScalarGen ⊎ Gen n —
--      the extension presentation of ⟨ω⟩ ≅ ℤ/8 by the Clifford group mod
--      scalars, with ω the generator of the cyclic factor and the gates
--      taken from SympGate.
--
-- So the two alphabets are the same set differently packaged: ExactGate
-- is ω plus SympGate, and ScalarGen ⊎ Gen n is the same split made with
-- a sum.  The translations are therefore a RELABELLING in each
-- direction, and most of the work is bookkeeping about which side a
-- letter came from.
--
-- The method is Examples.Groups.Symplectic.Simplified.Iso's, but there
-- the two rule sets share a generating set outright and the isomorphism
-- is the identity on words.  Here they differ, so — as in
-- Qubit.Selinger.Iso, one layer down — the builder is
-- Presentation.Morphism.GroupMorphism.StarGroupIsomorphism, which takes
-- a translation in each direction.
--
-- Where the two halves come from.
--
--   f-well-defined  the scalar relation ω⁸ = 1 is C1 up to bracketing;
--                   the conjugation relation is a single application of
--                   Circuit.Base's comm₀, since ω is 0-ary on the
--                   Figure-8 side; and each twisted relator is its
--                   Figure-8 namesake with the correction moved from the
--                   right of the equation to the left by ω^-central.
--                   That last family is Selinger.ScalarKernel.srel-kernel
--                   read forwards — the exponents in `corr` were copied
--                   from it — so `fwd-tw` below and that lemma should be
--                   read together.
--
--   g-well-defined  the converse.  C4 is where the scalar generator
--                   meets the gates, and after it C1, C10 and C11 go
--                   through by moving a scalar word past a gate word
--                   (ext-comm, the conjugation axiom iterated).  cω↑ is
--                   the pleasant case: the extension's scalar generator
--                   does not depend on the width at all, so both sides
--                   translate to the same word and it is refl.
--
-- The shift.  Figure 8's cong↑ has no counterpart in the extension rule
-- set, so `lemma-shift` moves a whole extension derivation up one wire.
-- Its twisted-relator case is exact — corr (cong↑ r) is corr r on the
-- nose — and its conjugation case is the same axiom one wire up, because
-- conj is constant.
--
-- Width.  Everything here holds at every width, width 0 included.  That
-- is new: when ω was the derived word (SH)³ it needed a wire to live on,
-- and the width-0 instance of this comparison was false (Figure 8
-- presented the trivial group while _Exact, 0 ===_ presented ℤ/8).  With
-- ω 0-ary both sides have their scalar at every width and the two agree
-- there too.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Exact-Iso-CMS where

open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _^'_ ; _ʷ ; wmap)

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)

import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Presentation.Morphism using (module GroupMorphism)
open import Presentation.Construct.Base
  using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ ; ConjRelʷ)
open import Presentation.Construct.Properties.Extension using (tw)
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

import Examples.Groups.Cyclic.Syntactics as CyS

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (SympGate) renaming (Gen to GenS ; _↥ to _↥ˢ ; _↑ to _↑ˢ)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8 using (ExactGate ; ω-gate ; _CRel,_===_ ; _≈ᶠ_ ; srel ; comm₀)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime
  as MS

open import Examples.Groups.Clifford.Qubit.Exact-Presentation
  using (ScalarGen ; Scalar-relation ; _Exact,_===_ ; conj ; corr ; ω ; ω⁻¹)

private
  variable
    m n : ℕ

  -- The associativity solver at each rule set.
  module AF (k : ℕ) = Assoc (k F8.CRel,_===_)
  module AE (k : ℕ) = Assoc (k Exact,_===_)
  module AS         = Assoc Scalar-relation

-- The extension alphabet, and its congruence.
Alph : ℕ → Set
Alph n = ScalarGen ⊎ GenS n

infix 4 _≈ₑ_
_≈ₑ_ : {n : ℕ} → Word (Alph n) → Word (Alph n) → Set
_≈ₑ_ {n} = PB._≈_ (n Exact,_===_)

------------------------------------------------------------------------
-- The two translations
--
-- ExactGate is ω-gate plus SympGate, so on gates the maps are the
-- identity under a change of constructor, and the scalar is matched with
-- the generator of the cyclic factor.

gate→ : SympGate m → ExactGate m
gate→ Symplectic.H-gate  = F8.H-gate
gate→ Symplectic.S-gate  = F8.S-gate
gate→ Symplectic.CZ-gate = F8.CZ-gate

-- A Symplectic generator, relabelled.  SympGate has no 0-ary gate, so
-- the gate₀ case is absurd.
sym→ex : GenS n → F8.Gen n
sym→ex (Symplectic.gate₀ ())
sym→ex (Symplectic.gate₁ h) = F8.gate₁ (gate→ h)
sym→ex (Symplectic.gate₂ h) = F8.gate₂ (gate→ h)
sym→ex (x ↥ˢ)               = sym→ex x F8.↥

f : Alph n → Word (F8.Gen n)
f (inj₁ _) = F8.ω
f (inj₂ x) = [ sym→ex x ]ʷ

-- Shifting an extension word up one wire: the scalar is
-- width-independent and stays put, the gates shift.
shift-sum : Alph n → Alph (₁₊ n)
shift-sum (inj₁ s) = inj₁ s
shift-sum (inj₂ x) = inj₂ (x ↥ˢ)

⇑ : Word (Alph n) → Word (Alph (₁₊ n))
⇑ = wmap shift-sum

g : F8.Gen n → Word (Alph n)
g (F8.gate₀ ω-gate)          = [ inj₁ tt ]ʷ
g (F8.gate₁ F8.H-gate)       = [ inj₂ (Symplectic.gate₁ Symplectic.H-gate) ]ʷ
g (F8.gate₁ F8.S-gate)       = [ inj₂ (Symplectic.gate₁ Symplectic.S-gate) ]ʷ
g (F8.gate₂ F8.CZ-gate)      = [ inj₂ (Symplectic.gate₂ Symplectic.CZ-gate) ]ʷ
g (x F8.↥)                   = ⇑ (g x)

-- The relabelling of a whole Symplectic circuit, and of a whole
-- Figure-8 circuit.
E : Word (GenS n) → Word (F8.Gen n)
E = wmap sym→ex

G : Word (F8.Gen n) → Word (Alph n)
G = g ʷ

------------------------------------------------------------------------
-- How the translations meet the embeddings

fᵣ : (w : Word (GenS n)) → (f ʷ) [ w ]ᵣ ≡ E w
fᵣ [ x ]ʷ  = Eq.refl
fᵣ ε       = Eq.refl
fᵣ (u • v) rewrite fᵣ u | fᵣ v = Eq.refl

-- E commutes with the shift, on the nose.
E-↑ : (w : Word (GenS n)) → E (w ↑ˢ) ≡ (E w) F8.↑
E-↑ [ x ]ʷ  = Eq.refl
E-↑ ε       = Eq.refl
E-↑ (u • v) rewrite E-↑ u | E-↑ v = Eq.refl

-- G commutes with the shift, on the nose: g of a shifted generator is
-- ⇑ of g, by definition, and both maps distribute over concatenation.
G-↑ : (w : Word (F8.Gen n)) → G (w F8.↑) ≡ ⇑ (G w)
G-↑ [ x ]ʷ  = Eq.refl
G-↑ ε       = Eq.refl
G-↑ (u • v) rewrite G-↑ u | G-↑ v = Eq.refl

-- The round trip on the Symplectic side is exact.
ex∘sym : (x : GenS n) → g (sym→ex x) ≡ [ inj₂ x ]ʷ
ex∘sym (Symplectic.gate₀ ())
ex∘sym (Symplectic.gate₁ Symplectic.H-gate)  = Eq.refl
ex∘sym (Symplectic.gate₁ Symplectic.S-gate)  = Eq.refl
ex∘sym (Symplectic.gate₂ Symplectic.CZ-gate) = Eq.refl
ex∘sym (x ↥ˢ) rewrite ex∘sym x = Eq.refl

------------------------------------------------------------------------
-- f-well-defined
--
-- Three axiom families; the EmptyRel factor contributes none.

-- The translated scalar word survives the shift.  ω is the same on every
-- wire (Figure8.cω↑), so a word in it lifts to itself — and, ω being
-- 0-ary, this holds at every width.
fₗ-↑ : (c : Word ScalarGen) →
       (((f {n} ʷ) [ c ]ₗ) F8.↑) ≈ᶠ ((f {₁₊ n} ʷ) [ c ]ₗ)
fₗ-↑ [ _ ]ʷ  = F8.ω↑≈ω
fₗ-↑ ε       = PB.refl
fₗ-↑ (c • d) = PB.cong (fₗ-↑ c) (fₗ-↑ d)

-- A relator that Figure 8 and its quotient share needs no scalar.
shared : {u v : Word (F8.Gen n)} → u ≈ᶠ v → u ≈ᶠ (ε • v)
shared e = PB.trans e (PB.sym PB.left-unit)

-- Each mod-scalar axiom, with its correction moved to the left.
srel-fwd : {u v : Word (GenS n)} (r : (n MS.Sel, u === v)) →
           E u ≈ᶠ ((f ʷ) [ corr (MS.srel r) ]ₗ • E v)
srel-fwd MS.c2  = shared (PB.axiom (srel F8.c2))
srel-fwd MS.c3  = shared (PB.axiom (srel F8.c3))
srel-fwd MS.c5  = shared (PB.axiom (srel F8.c5))
srel-fwd MS.c6  = shared (PB.axiom (srel F8.c6))
srel-fwd MS.c7  = shared (PB.axiom (srel F8.c7))
srel-fwd MS.c8  = shared (PB.axiom (srel F8.c8))
srel-fwd MS.c9  = shared (PB.axiom (srel F8.c9))
srel-fwd MS.c12 = shared (PB.axiom (srel F8.c12))
srel-fwd MS.c13 = shared (PB.axiom (srel F8.c13))
srel-fwd MS.c14 = shared (PB.axiom (srel F8.c14))
srel-fwd MS.c15 = shared (PB.axiom (srel F8.c15))

-- C4: mod scalars (SH)³ = 1; in Figure 8 that word is ω.
srel-fwd MS.c4 = PB.trans (PB.axiom (srel F8.c4)) (PB.sym PB.right-unit)

-- C10 / C11: Figure 8 keeps a trailing ω⁻¹; the quotient drops it.  Take
-- the Figure-8 axiom, re-bracket its right-hand side as (rhs • ω⁷), and
-- walk the scalar to the front.
srel-fwd (MS.c10 {n}) =
  PB.trans (AF.by-assoc-and (₂₊ n) (PB.axiom (srel F8.c10)) Eq.refl Eq.refl)
           (PB.sym (F8.ω^-central 7 _))
srel-fwd (MS.c11 {n}) =
  PB.trans (AF.by-assoc-and (₂₊ n) (PB.axiom (srel F8.c11)) Eq.refl Eq.refl)
           (PB.sym (F8.ω^-central 7 _))

fwd-tw : {a b : Word (GenS n)} (r̄ : (n MS.CRel, a === b)) →
         E a ≈ᶠ ((f ʷ) [ corr r̄ ]ₗ • E b)
fwd-tw (MS.srel r) = srel-fwd r
fwd-tw (MS.cong↑ {w = u} {v = v} r̄) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (E-↑ u))
            (Eq.cong ((f ʷ) [ corr r̄ ]ₗ •_) (Eq.sym (E-↑ v)))
            (PB.trans (F8.lemma-cong↑ _ _ (fwd-tw r̄))
                      (PB.cong (fₗ-↑ (corr r̄)) PB.refl))
fwd-tw (MS.comm₁ h gg) = shared (PB.axiom (F8.comm₁ (gate→ h) (sym→ex gg)))
fwd-tw (MS.comm₂ h gg) = shared (PB.axiom (F8.comm₂ (gate→ h) (sym→ex gg)))

f-well-defined : {a b : Word (Alph n)} → (n Exact,_===_) a b →
                 (f ʷ) a ≈ᶠ (f ʷ) b
-- ω⁸ = 1 is C1, up to the cyclic presentation's left-associated powers.
f-well-defined {n} (_⋄_⋄_.left CyS.order) =
  AF.by-assoc-and n (PB.axiom (srel F8.c1)) Eq.refl Eq.refl
f-well-defined (_⋄_⋄_.right ())
-- Centrality: one application of the structural comm₀.
f-well-defined (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm y x))) =
  PB.axiom (comm₀ ω-gate (sym→ex x))
f-well-defined (_⋄_⋄_.mid (_∪_.right (tw {u} {v} r̄))) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (fᵣ u))
            (Eq.cong ((f ʷ) [ corr r̄ ]ₗ •_) (Eq.sym (fᵣ v)))
            (fwd-tw r̄)

f-left-inv-gen : (y : F8.Gen n) → [ y ]ʷ ≈ᶠ ((f ʷ) (g y))
f-left-inv-gen (F8.gate₀ ω-gate)     = PB.refl
f-left-inv-gen (F8.gate₁ F8.H-gate)  = PB.refl
f-left-inv-gen (F8.gate₁ F8.S-gate)  = PB.refl
f-left-inv-gen (F8.gate₂ F8.CZ-gate) = PB.refl
f-left-inv-gen (y F8.↥)              =
  PB.trans (F8.lemma-cong↑ _ _ (f-left-inv-gen y)) (f-⇑ (g y))
  where
  -- (f ʷ) commutes with the shift, up to cω↑ on the scalar letters.
  f-⇑ : (w : Word (Alph m)) → (((f ʷ) w) F8.↑) ≈ᶠ ((f ʷ) (⇑ w))
  f-⇑ [ inj₁ _ ]ʷ = F8.ω↑≈ω
  f-⇑ [ inj₂ _ ]ʷ = PB.refl
  f-⇑ ε           = PB.refl
  f-⇑ (u • v)     = PB.cong (f-⇑ u) (f-⇑ v)

------------------------------------------------------------------------
-- Working inside the extension presentation

-- A twisted mod-scalar relator.
twist : {u v : Word (GenS n)} (r̄ : (n MS.CRel, u === v)) →
        [ u ]ᵣ ≈ₑ ([ corr r̄ ]ₗ • [ v ]ᵣ)
twist r̄ = PB.axiom (_⋄_⋄_.mid (_∪_.right (tw r̄)))

-- A twisted relator whose correction is trivial.
twistε : {u v : Word (GenS n)} (r̄ : (n MS.CRel, u === v)) →
         corr r̄ ≡ ε → [ u ]ᵣ ≈ₑ [ v ]ᵣ
twistε r̄ eq = PB.trans (Eq.subst (λ □ → _ ≈ₑ ([ □ ]ₗ • _)) eq (twist r̄))
                       PB.left-unit

-- Moving a gate rightwards past the scalar generator.
conj-ax : (x : GenS n) →
          ([ [ x ]ʷ ]ᵣ • [ ω ]ₗ) ≈ₑ ([ ω ]ₗ • [ [ x ]ʷ ]ᵣ)
conj-ax x = PB.axiom (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm tt x)))

-- The scalar congruence, along the left embedding.
lefts : {u v : Word ScalarGen} → PB._≈_ Scalar-relation u v →
        _≈ₑ_ {n} [ u ]ₗ [ v ]ₗ
lefts PB.refl         = PB.refl
lefts (PB.sym h)      = PB.sym (lefts h)
lefts (PB.trans h h₁) = PB.trans (lefts h) (lefts h₁)
lefts (PB.cong h h₁)  = PB.cong (lefts h) (lefts h₁)
lefts PB.assoc        = PB.assoc
lefts PB.left-unit    = PB.left-unit
lefts PB.right-unit   = PB.right-unit
lefts (PB.axiom x)    = PB.axiom (_⋄_⋄_.left x)

-- Every word commutes with the scalar generator: a gate letter by the
-- conjugation axiom, a scalar letter because both sides are then the
-- same two-letter word.
ext-comm1 : (w : Word (Alph n)) → (w • [ inj₁ tt ]ʷ) ≈ₑ ([ inj₁ tt ]ʷ • w)
ext-comm1 [ inj₁ tt ]ʷ = PB.refl
ext-comm1 [ inj₂ x ]ʷ  = conj-ax x
ext-comm1 ε            = PB.trans PB.left-unit (PB.sym PB.right-unit)
ext-comm1 (u • v) =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (ext-comm1 v))
      (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (ext-comm1 u) PB.refl) PB.assoc)))

-- … and hence with any scalar word.
ext-comm : (w : Word (Alph n)) (c : Word ScalarGen) →
           (w • [ c ]ₗ) ≈ₑ ([ c ]ₗ • w)
ext-comm w [ tt ]ʷ = ext-comm1 w
ext-comm w ε       = PB.trans PB.right-unit (PB.sym PB.left-unit)
ext-comm w (c • d) =
  PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (ext-comm w c) PB.refl)
      (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl (ext-comm w d)) (PB.sym PB.assoc))))

------------------------------------------------------------------------
-- Shifting an extension derivation up one wire

⇑ᵣ : (w : Word (GenS n)) → ⇑ [ w ]ᵣ ≡ [ w ↑ˢ ]ᵣ
⇑ᵣ [ x ]ʷ  = Eq.refl
⇑ᵣ ε       = Eq.refl
⇑ᵣ (u • v) = Eq.cong₂ _•_ (⇑ᵣ u) (⇑ᵣ v)

⇑ₗ : (c : Word ScalarGen) → ⇑ {n} [ c ]ₗ ≡ [ c ]ₗ
⇑ₗ [ _ ]ʷ  = Eq.refl
⇑ₗ ε       = Eq.refl
⇑ₗ (c • d) = Eq.cong₂ _•_ (⇑ₗ c) (⇑ₗ d)

-- Each axiom family survives the shift.  The scalar relation is
-- width-free; the conjugation axiom becomes the same axiom for the
-- shifted gate, conj being constant; and a twisted relator becomes the
-- twisted relator of cong↑, whose correction is the same word.
-- (subst rather than rewrite throughout: the equations are about the
-- constructor's own words, which rewrite will not abstract over.)
shift-ax : {a b : Word (Alph n)} → (n Exact,_===_) a b → (⇑ a) ≈ₑ (⇑ b)
shift-ax (_⋄_⋄_.left {u} {v} x) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (⇑ₗ u)) (Eq.sym (⇑ₗ v))
            (PB.axiom (_⋄_⋄_.left x))
shift-ax (_⋄_⋄_.right ())
shift-ax (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm tt x))) =
  PB.axiom (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm tt (x ↥ˢ))))
shift-ax (_⋄_⋄_.mid (_∪_.right (tw {u} {v} r̄))) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (⇑ᵣ u))
            (Eq.sym (Eq.cong₂ _•_ (⇑ₗ (corr r̄)) (⇑ᵣ v)))
            (twist (MS.cong↑ r̄))

lemma-shift : {a b : Word (Alph n)} → a ≈ₑ b → (⇑ a) ≈ₑ (⇑ b)
lemma-shift PB.refl         = PB.refl
lemma-shift (PB.sym h)      = PB.sym (lemma-shift h)
lemma-shift (PB.trans h h₁) = PB.trans (lemma-shift h) (lemma-shift h₁)
lemma-shift (PB.cong h h₁)  = PB.cong (lemma-shift h) (lemma-shift h₁)
lemma-shift PB.assoc        = PB.assoc
lemma-shift PB.left-unit    = PB.left-unit
lemma-shift PB.right-unit   = PB.right-unit
lemma-shift (PB.axiom x)    = shift-ax x

-- A once-shifted word commutes with a 1-ary gate on the bottom wire: a
-- scalar letter by the conjugation axiom, a shifted gate letter by the
-- mod-scalar comm₁.
shifted-comm₁ : (h : SympGate 1) (w : Word (Alph n)) →
                (⇑ w • [ [ Symplectic.gate₁ h ]ʷ ]ᵣ)
                  ≈ₑ ([ [ Symplectic.gate₁ h ]ʷ ]ᵣ • ⇑ w)
shifted-comm₁ h [ inj₁ tt ]ʷ = PB.sym (conj-ax (Symplectic.gate₁ h))
shifted-comm₁ h [ inj₂ x ]ʷ  = twistε (MS.comm₁ h x) Eq.refl
shifted-comm₁ h ε            = PB.trans PB.left-unit (PB.sym PB.right-unit)
shifted-comm₁ h (u • v) =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (shifted-comm₁ h v))
      (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (shifted-comm₁ h u) PB.refl) PB.assoc)))

-- The same, twice shifted, against CZ.
shifted-comm₂ : (w : Word (Alph n)) →
                (⇑ (⇑ w) • [ [ Symplectic.gate₂ Symplectic.CZ-gate ]ʷ ]ᵣ)
                  ≈ₑ ([ [ Symplectic.gate₂ Symplectic.CZ-gate ]ʷ ]ᵣ • ⇑ (⇑ w))
shifted-comm₂ [ inj₁ tt ]ʷ =
  PB.sym (conj-ax (Symplectic.gate₂ Symplectic.CZ-gate))
shifted-comm₂ [ inj₂ x ]ʷ  = twistε (MS.comm₂ Symplectic.CZ-gate x) Eq.refl
shifted-comm₂ ε            = PB.trans PB.left-unit (PB.sym PB.right-unit)
shifted-comm₂ (u • v) =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (shifted-comm₂ v))
      (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (shifted-comm₂ u) PB.refl) PB.assoc)))

------------------------------------------------------------------------
-- g-well-defined
--
-- Every Figure-8 axiom, translated.  G of a Figure-8 word built from
-- gates is the right embedding of the corresponding Symplectic word, so
-- most cases are a twisted relator with a trivial correction.

g-wd-ax : {u v : Word (F8.Gen n)} → (n F8.CRel, u === v) → G u ≈ₑ G v

-- C1: ω⁸ = 1 is the cyclic order relation, up to bracketing.  The words
-- are given explicitly: unifying [ u ]ₗ with a translated word would ask
-- Agda to invert a wmap.
g-wd-ax {n} (srel F8.c1) = lefts {n = n} {u = ω ^ 8} {v = ε} scalar-8
  where
  scalar-8 : PB._≈_ Scalar-relation (ω ^ 8) ε
  scalar-8 = AS.by-assoc-and (PB.axiom CyS.order) Eq.refl Eq.refl

g-wd-ax (srel F8.c2)  = twistε (MS.srel MS.c2)  Eq.refl
g-wd-ax (srel F8.c3)  = twistε (MS.srel MS.c3)  Eq.refl
g-wd-ax (srel F8.c5)  = twistε (MS.srel MS.c5)  Eq.refl
g-wd-ax (srel F8.c6)  = twistε (MS.srel MS.c6)  Eq.refl
g-wd-ax (srel F8.c7)  = twistε (MS.srel MS.c7)  Eq.refl
g-wd-ax (srel F8.c8)  = twistε (MS.srel MS.c8)  Eq.refl
g-wd-ax (srel F8.c9)  = twistε (MS.srel MS.c9)  Eq.refl
g-wd-ax (srel F8.c12) = twistε (MS.srel MS.c12) Eq.refl
g-wd-ax (srel F8.c13) = twistε (MS.srel MS.c13) Eq.refl
g-wd-ax (srel F8.c14) = twistε (MS.srel MS.c14) Eq.refl
g-wd-ax (srel F8.c15) = twistε (MS.srel MS.c15) Eq.refl

-- C4: (SH)³ = ω.  This is the twisted relator for the mod-scalar C4,
-- whose correction is exactly the scalar generator.
g-wd-ax (srel F8.c4) = PB.trans (twist (MS.srel MS.c4)) PB.right-unit

-- C10 / C11: the twisted relator puts the correction on the left; move
-- it back to the right and re-bracket.
g-wd-ax (srel (F8.c10 {n})) =
  PB.trans (twist (MS.srel MS.c10))
    (PB.trans (PB.sym (ext-comm _ ω⁻¹)) (AE.by-assoc (₂₊ n) Eq.refl))
g-wd-ax (srel (F8.c11 {n})) =
  PB.trans (twist (MS.srel MS.c11))
    (PB.trans (PB.sym (ext-comm _ ω⁻¹)) (AE.by-assoc (₂₊ n) Eq.refl))

-- cω↑: the extension's scalar generator does not depend on the width, so
-- both sides translate to the same word.
g-wd-ax (srel F8.cω↑) = PB.refl

-- The structural rules.  comm₀ is centrality, which on this side is
-- ext-comm1; comm₁ and comm₂ are their mod-scalar namesakes, after a
-- case split to make g reduce on the gate.
g-wd-ax (comm₀ ω-gate y) = ext-comm1 (g y)
g-wd-ax (F8.comm₁ F8.H-gate y) = shifted-comm₁ Symplectic.H-gate (g y)
g-wd-ax (F8.comm₁ F8.S-gate y) = shifted-comm₁ Symplectic.S-gate (g y)
g-wd-ax (F8.comm₂ F8.CZ-gate y) = shifted-comm₂ (g y)
g-wd-ax (F8.cong↑ {w = u} {v = v} r) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (G-↑ u)) (Eq.sym (G-↑ v))
            (lemma-shift (g-wd-ax r))

g-well-defined : {u v : Word (F8.Gen n)} → (n F8.CRel, u === v) →
                 (g ʷ) u ≈ₑ (g ʷ) v
g-well-defined = g-wd-ax

g-left-inv-gen : (a : Alph n) → [ a ]ʷ ≈ₑ ((g ʷ) (f a))
g-left-inv-gen (inj₁ tt)     = PB.refl
g-left-inv-gen {n} (inj₂ x)  =
  PB.refl' (n Exact,_===_) (Eq.sym (ex∘sym x))

------------------------------------------------------------------------
-- Group-likeness of the two rule sets

grouplike-F8 : Grouplike (n F8.CRel,_===_)
grouplike-F8 {n} (F8.gate₀ ω-gate) =
  F8.ω ^ 7 , AF.by-assoc-and n (PB.axiom (srel F8.c1)) Eq.refl Eq.refl
grouplike-F8 (F8.gate₁ F8.H-gate)  =
  F8.H , PB.axiom (srel F8.c2)
grouplike-F8 (F8.gate₂ F8.CZ-gate) =
  F8.CZ , PB.axiom (srel F8.c5)
grouplike-F8 {n} (F8.gate₁ F8.S-gate) =
  F8.S • F8.S • F8.S , AF.by-assoc-and n (PB.axiom (srel F8.c3)) Eq.refl Eq.refl
grouplike-F8 (y F8.↥) with grouplike-F8 y
... | inv , eq = inv F8.↑ , F8.lemma-cong↑ (inv • [ y ]ʷ) ε eq

grouplike-Ex : Grouplike (n Exact,_===_)
grouplike-Ex {n} (inj₁ tt) =
  [ ω ^' 7 ]ₗ ,
  lefts {n = n} {u = ω ^' 7 • ω} {v = ε} (proj₂ (CyS.grouplike 7 tt))
grouplike-Ex (inj₂ (Symplectic.gate₀ ()))
grouplike-Ex (inj₂ (Symplectic.gate₁ Symplectic.H-gate)) =
  [ Symplectic.H ]ᵣ , twistε (MS.srel MS.c2) Eq.refl
grouplike-Ex (inj₂ (Symplectic.gate₂ Symplectic.CZ-gate)) =
  [ Symplectic.CZ ]ᵣ , twistε (MS.srel MS.c5) Eq.refl
grouplike-Ex {n} (inj₂ (Symplectic.gate₁ Symplectic.S-gate)) =
  [ Symplectic.S • Symplectic.S • Symplectic.S ]ᵣ ,
  PB.trans (AE.by-assoc n Eq.refl) (twistε (MS.srel MS.c3) Eq.refl)
grouplike-Ex (inj₂ (x ↥ˢ)) with grouplike-Ex (inj₂ x)
... | inv , eq = ⇑ inv , lemma-shift eq

------------------------------------------------------------------------
-- The isomorphism
--
-- Both translations are well defined and invert each other on
-- generators, so the two rule sets present the same group and the
-- isomorphism is (f ʷ).

module Iso (n : ℕ) where

  private
    module GM = GroupMorphism (n Exact,_===_) (n F8.CRel,_===_)
                  grouplike-Ex grouplike-F8

  open GM.StarGroupIsomorphism f g
         f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen
    public using (isGroupIsomorphism)

-- The headline, in the shape Simplified.Iso states its own: the word
-- group of the extension presentation is isomorphic to the word group of
-- Figure 8, by the translation (f ʷ).
open GroupMorphisms

Theorem-Exact-iso-F8 : ∀ {n} →
  let module G1 = Group-Lemmas (n Exact,_===_)    grouplike-Ex
      module G2 = Group-Lemmas (n F8.CRel,_===_)  grouplike-F8
  in IsGroupIsomorphism (Group.rawGroup G1.•-ε-group)
                        (Group.rawGroup G2.•-ε-group) (f {n} ʷ)
Theorem-Exact-iso-F8 {n} = Iso.isGroupIsomorphism n
