------------------------------------------------------------------------
-- Presentations of groups
--
-- The exact qupit Clifford rule set presents the central extension it
-- was built from:
--
--     (n Exact,_===_)  IsPresentationOf  Presented-group n gd.
--
-- On the left is Clifford.Qupit.Syntactics: the scalar ω and the gates,
-- with the cyclic relation ωᵖ = 1, centrality of ω, and the sixteen
-- Paper-V0 relations each twisted by its power of ω (only order-SH
-- carries one).  On the right is Clifford.Qupit.Semantics.Presented-
-- Extension: the group A ×_γᶜ H whose kernel A is the scalars presented
-- by ⟨ ω ∣ ωᵖ = 1 ⟩, whose quotient H is the Paper-V0 rule set, and
-- whose cocycle γᶜ comes from the generator data through CocycleGen.
--
-- The general statement below takes two hypotheses, both already named
-- by Semantics, and no others — and BOTH ARE NOW SUPPLIED, so the
-- theorem at the end of the file (`presentation-exact`) has none:
--
--   gd    the generator data, which is what γᶜ — hence the group — is
--         built from, so it cannot be dispensed with here;
--   real  Presented-Extension.Realises, that the cocycle realises corr:
--         reading a circuit in the total group with every gate lifted
--         trivially makes the two sides of a Paper-V0 relation differ by
--         exactly the correction word `corr` records.  Without it the
--         theorem is false — the split cocycle is a cocycle too, and
--         Semantics.split-forces shows it cannot realise corr.
--
-- Why no normal forms.  Proposition 2.55 (Presentation.Construct.
-- Properties.Extension) proves the same statement for an arbitrary
-- extension, but it asks each factor for a BIJECTIVE normal form,
-- because its completeness argument is a Reidemeister–Schreier coset
-- enumeration over the quotient's canonical representatives.  For the
-- qupit quotient no such normal form exists yet (nothing in
-- ProjectiveClifford.Qupit has one), and it is not needed: HERE the two
-- factors are word groups, so the interpretation
--
--     ⟦_⟧ : Word (ScalarGen ⊎ Gen n) → Word ScalarGen × Circuit n
--
-- is a splitting rather than a normalisation, and completeness follows
-- from three facts about words alone.
--
--   * `split` — every word is ≈ [ scalars ]ₗ • [ gates ]ᵣ, since ω is
--     central.  This is where the qupit case is easier than the general
--     one: conj is constant, so nothing is conjugated as a scalar
--     crosses a gate and the split needs no bookkeeping;
--   * `corr-witness` — a quotient derivation a ≈q b, embedded on the
--     right, leaves a correction in the kernel: [ a ]ᵣ ≈ [ w ]ₗ • [ b ]ᵣ
--     for a word w built by recursion on the derivation.  This is
--     Extension.corr-witness, specialised: the `cong` case conjugates
--     nothing, again by centrality;
--   * `scal-corr` — that correction is exactly the scalar defect the
--     cocycle accumulates.  Not a second induction: it is the previous
--     item pushed through SOUNDNESS, which is where `real` is spent.
--
-- Completeness is then cancellation in the kernel: two words with the
-- same denotation have quotient-equal gate parts, whose correction
-- makes up precisely the difference of their scalar parts.  Surjectivity
-- is the same splitting read backwards, correcting the scalar by the
-- inverse of the defect.
--
-- The result is assembled as a MONOID presentation and promoted by
-- Presentation.Definitions.monoidPresentation⇒presentation, since the
-- interpretation preserves • and ε on the nose (the product of the
-- central extension IS pairing, twisted) and grouplikeness of the exact
-- alphabet is the one remaining input — a scalar generator inverts in
-- the cyclic factor, a gate in the Paper-V0 factor up to its correction.
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

module Examples.Groups.Clifford.Qupit.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function.Definitions using (Surjective)
open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
open import Presentation.Construct.Base
  using ([_]ₗ ; [_]ᵣ ; EmptyRel ; ConjRelʷ ; comm ; left ; right ; mid
        ; module LeftRightCongruence)
import Presentation.Construct.Properties.Extension as Ext
open Ext using (tw)
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsMonoidPresentationOf_
        ; monoidPresentation⇒presentation)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)

import Normalization.StarInterp

import ForStdlib.Algebra.Construct.CentralExtension as CE
open CE using (Cocycle)

-- The scalar alphabet's grouplike witness.
import Examples.Groups.Cyclic.Syntactics as Cy

-- The quotient's grouplike witness.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  p-3 p-prime g* g-gen as PapL

-- The syntax: ScalarGen, ω, Scalar-relation, conj, corr, _Exact,_===_.
import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS

-- The semantics: A, H, the cocycle, the total group, and Realises.
import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem
module PE = Sem.Presented-Extension g* g-gen

-- The generator data, built from the Weyl cocycle, and the reduction of
-- Realises to arithmetic in ℤ/pℤ.
import Examples.Groups.Clifford.Qupit.SemFE p-3 p-prime g* g-gen as FE
import Examples.Groups.Clifford.Qupit.SemRealises p-3 p-prime g* g-gen as RL

-- ... and the sixteen equations in ℤ/pℤ that Realises reduces to,
-- proved.
import Examples.Groups.Clifford.Qupit.SemSRel p-3 p-prime g* g-gen as SR

------------------------------------------------------------------------
-- The two grouplike witnesses
--
-- Both factors are word groups, so their inverses are the ones their own
-- presentations supply: ω⁻¹ = ω^(p-1) on the scalar side, and Paper-V0's
-- own witness on the gate side.

glS : Grouplike QS.Scalar-relation
glS = Cy.grouplike p-1

glQ : ∀ {n} → Grouplike (QS.CR._QRel,_===_ n)
glQ {n} = PapL.Paper-GroupLike.grouplike {n}

------------------------------------------------------------------------
-- Proposition 2.55 at the presented central extension
--
-- Everything is stated at a fixed width, and against the two hypotheses
-- the group itself is built from.  `gd` stays a module PARAMETER: a
-- concrete cocycle would have to be normalised at every conversion
-- check, which is the discipline Qubit.SemCentralExt's header measures.

module Exact-Presentation
  (n : ℕ)
  (gd : PE.GeneratorData n)
  (real : PE.Realises n gd)
  where

  ----------------------------------------------------------------------
  -- Names

  private
    -- The kernel's relation, the quotient's, and the exact one.
    S : WRel QS.ScalarGen
    S = QS.Scalar-relation

    Q : WRel (QS.Gen n)
    Q = QS.CR._QRel,_===_ n

    Γ : WRel (QS.ScalarGen ⊎ QS.Gen n)
    Γ = QS._Exact,_===_ n

    module KB = PB S
    module QB = PB Q
    module EB = PB Γ

    module GD = PE.GeneratorData gd
    module GS = Group-Lemmas S glS

    -- The total group, its two factors, and the reading of a circuit in
    -- it that `real` speaks about.
    module A = AbelianGroup (PE.A n)
    module H = Group (PE.H n)
    module Ev = PE.Evaluation n (PE.γᶜ n gd)

  G : Group 0ℓ 0ℓ
  G = PE.Presented-group n gd

  private
    module G = Group G

    open LeftRightCongruence S EmptyRel (Ext.extp S Q QS.conj QS.corr)
      using (lefts)

    ------------------------------------------------------------------
    -- Equality in the total group is a pair
    --
    -- Pointwise, so the three combinators below are the two factors'
    -- read componentwise.  Written out rather than taken from `G`
    -- because the implicits of a Pointwise equivalence are never
    -- recovered by unification.

    infixr 4 _⟨G⟩_
    _⟨G⟩_ : ∀ {x y z} → G._≈_ x y → G._≈_ y z → G._≈_ x z
    (e₁ , e₂) ⟨G⟩ (f₁ , f₂) = KB.trans e₁ f₁ , QB.trans e₂ f₂

    G-refl : ∀ {x} → G._≈_ x x
    G-refl = KB.refl , QB.refl

    G-sym : ∀ {x y} → G._≈_ x y → G._≈_ y x
    G-sym (e₁ , e₂) = KB.sym e₁ , QB.sym e₂

    G-∙ : ∀ {x x' y y'} → G._≈_ x x' → G._≈_ y y' →
          G._≈_ (x G.∙ y) (x' G.∙ y')
    G-∙ (e₁ , e₂) (f₁ , f₂) =
        KB.cong (KB.cong e₁ f₁) (Cocycle.c-cong (PE.γᶜ n gd) e₂ f₂)
      , QB.cong e₂ f₂

  ----------------------------------------------------------------------
  -- The interpretation
  --
  -- A scalar generator is the scalar ω with no gate, a gate is the gate
  -- with no scalar; the monoid extension is what accumulates the
  -- cocycle.

  ⟦_⟧₀ : (QS.ScalarGen ⊎ QS.Gen n) → G.Carrier
  ⟦ inj₁ x ⟧₀ = [ x ]ʷ , ε
  ⟦ inj₂ a ⟧₀ = ε , [ a ]ʷ

  private
    module SIΓ = Normalization.StarInterp Γ
    module IE = SIΓ.Extend (Group.monoid G) ⟦_⟧₀

  ⟦_⟧ : Word (QS.ScalarGen ⊎ QS.Gen n) → G.Carrier
  ⟦_⟧ = IE.⟦_⟧

  ----------------------------------------------------------------------
  -- The two embeddings
  --
  -- A left-embedded word is its scalar with no gate — up to the cocycle,
  -- which vanishes on the trivial gate.  A right-embedded word is read
  -- exactly as Semantics.Evaluation reads it, on the nose, which is what
  -- lets `real` be applied without transport.

  private
    emb-l : (a : Word QS.ScalarGen) → G._≈_ ⟦ [ a ]ₗ ⟧ (a , ε)
    emb-l [ x ]ʷ  = G-refl
    emb-l ε       = G-refl
    emb-l (a • b) =
      G-∙ (emb-l a) (emb-l b) ⟨G⟩ (KB.right-unit , QB.left-unit)

    emb-r : (w : QS.Circuit n) → ⟦ [ w ]ᵣ ⟧ ≡ Ev.⟦ w ⟧
    emb-r [ a ]ʷ  = Eq.refl
    emb-r ε       = Eq.refl
    emb-r (u • v) = Eq.cong₂ G._∙_ (emb-r u) (emb-r v)

    -- A circuit's gate part is the circuit itself: the second component
    -- never sees the cocycle.
    gate : (w : QS.Circuit n) → proj₂ Ev.⟦ w ⟧ ≡ w
    gate [ a ]ʷ  = Eq.refl
    gate ε       = Eq.refl
    gate (u • v) = Eq.cong₂ _•_ (gate u) (gate v)

    ev-pair : (w : QS.Circuit n) → G._≈_ Ev.⟦ w ⟧ (Ev.scal w , w)
    ev-pair w = KB.refl , QB.refl' (gate w)

    emb-r-pair : (w : QS.Circuit n) → G._≈_ ⟦ [ w ]ᵣ ⟧ (Ev.scal w , w)
    emb-r-pair w =
      Eq.subst (λ z → G._≈_ z (Ev.scal w , w)) (Eq.sym (emb-r w)) (ev-pair w)

    -- A split word, evaluated.  The cocycle contributes nothing: it is
    -- normalised, and the left factor carries no gate.
    val : (a : Word QS.ScalarGen) (b : QS.Circuit n) →
          G._≈_ ⟦ [ a ]ₗ • [ b ]ᵣ ⟧ ((a • Ev.scal b) • ε , ε • b)
    val a b = G-∙ (emb-l a) (emb-r-pair b)

  ----------------------------------------------------------------------
  -- Soundness of the raw axioms
  --
  -- Three families.  The kernel's relations hold because the left
  -- embedding lands in the kernel; centrality holds because the cocycle
  -- is normalised and conj is constant; and the twisted relators are
  -- exactly `real`, which is the whole content of the theorem.

  private
    twisted : {u v : QS.Circuit n} (r : Q u v) →
              G._≈_ Ev.⟦ u ⟧ (⟦ [ QS.corr r ]ₗ ⟧ G.∙ Ev.⟦ v ⟧)
    twisted {u} {v} r =
      ev-pair u ⟨G⟩ step ⟨G⟩ G-sym (G-∙ (emb-l (QS.corr r)) (ev-pair v))
      where
      step : G._≈_ (Ev.scal u , u) ((QS.corr r , ε) G.∙ (Ev.scal v , v))
      step = KB.trans (real r) (KB.sym KB.right-unit)
           , QB.trans (QB.axiom r) (QB.sym QB.left-unit)

  sound-ax : ∀ {w v} → Γ w v → G._≈_ ⟦ w ⟧ ⟦ v ⟧
  sound-ax (left {u} {v} x) =
    emb-l u ⟨G⟩ (KB.axiom x , QB.refl) ⟨G⟩ G-sym (emb-l v)
  sound-ax (right ())
  sound-ax (mid (left (comm y x))) = first , second
    where
    first : KB._≈_ ((ε • [ y ]ʷ) • GD.G x ε) (([ y ]ʷ • ε) • ε)
    first = KB.trans (KB.cong KB.left-unit (GD.G-ε x)) (KB.sym KB.right-unit)
    second : QB._≈_ ([ x ]ʷ • ε) (ε • [ x ]ʷ)
    second = QB.trans QB.right-unit (QB.sym QB.left-unit)
  sound-ax (mid (right (tw {u} {v} r))) =
    Eq.subst₂ (λ z₁ z₂ → G._≈_ z₁ (⟦ [ QS.corr r ]ₗ ⟧ G.∙ z₂))
              (Eq.sym (emb-r u)) (Eq.sym (emb-r v)) (twisted r)

  private
    module IC = IE.Cong sound-ax

  sound : ∀ {w v} → EB._≈_ w v → G._≈_ ⟦ w ⟧ ⟦ v ⟧
  sound = IC.fʷ-cong

  ----------------------------------------------------------------------
  -- The scalar is central
  --
  -- The one axiom of the conjugation family, walked across two words.
  -- conj is the constant ω and the scalar alphabet is a singleton, so
  -- the axiom already reads as plain commutation and nothing has to be
  -- conjugated.

  private
    central1 : (x : QS.Gen n) (a : Word QS.ScalarGen) →
               EB._≈_ ([ [ x ]ʷ ]ᵣ • [ a ]ₗ) ([ a ]ₗ • [ [ x ]ʷ ]ᵣ)
    central1 x [ y ]ʷ  = EB.axiom (mid (left (comm y x)))
    central1 x ε       = EB.trans EB.right-unit (EB.sym EB.left-unit)
    central1 x (a • b) =
      EB.trans (EB.sym EB.assoc)
        (EB.trans (EB.cong (central1 x a) EB.refl)
          (EB.trans EB.assoc
            (EB.trans (EB.cong EB.refl (central1 x b)) (EB.sym EB.assoc))))

    central : (w : QS.Circuit n) (a : Word QS.ScalarGen) →
              EB._≈_ ([ w ]ᵣ • [ a ]ₗ) ([ a ]ₗ • [ w ]ᵣ)
    central [ x ]ʷ  a = central1 x a
    central ε       a = EB.trans EB.left-unit (EB.sym EB.right-unit)
    central (u • v) a =
      EB.trans EB.assoc
        (EB.trans (EB.cong EB.refl (central v a))
          (EB.trans (EB.sym EB.assoc)
            (EB.trans (EB.cong (central u a) EB.refl) EB.assoc)))

  ----------------------------------------------------------------------
  -- Splitting a word
  --
  -- Scalars to the left, gates to the right.  Because the scalars are
  -- central this is a plain partition of the letters — no conjugation,
  -- no correction — and it is what makes the interpretation a bijection
  -- onto pairs.

  private
    sw : Word (QS.ScalarGen ⊎ QS.Gen n) → Word QS.ScalarGen
    sw [ inj₁ x ]ʷ = [ x ]ʷ
    sw [ inj₂ a ]ʷ = ε
    sw ε           = ε
    sw (u • v)     = sw u • sw v

    gw : Word (QS.ScalarGen ⊎ QS.Gen n) → QS.Circuit n
    gw [ inj₁ x ]ʷ = ε
    gw [ inj₂ a ]ʷ = [ a ]ʷ
    gw ε           = ε
    gw (u • v)     = gw u • gw v

    split : (w : Word (QS.ScalarGen ⊎ QS.Gen n)) →
            EB._≈_ w ([ sw w ]ₗ • [ gw w ]ᵣ)
    split [ inj₁ x ]ʷ = EB.sym EB.right-unit
    split [ inj₂ a ]ʷ = EB.sym EB.left-unit
    split ε           = EB.sym EB.left-unit
    split (u • v) =
      EB.trans (EB.cong (split u) (split v))
        (EB.trans EB.assoc
          (EB.trans (EB.cong EB.refl (EB.sym EB.assoc))
            (EB.trans (EB.cong EB.refl (EB.cong (central (gw u) (sw v)) EB.refl))
              (EB.trans (EB.cong EB.refl EB.assoc) (EB.sym EB.assoc)))))

    ⟦⟧-split : (w : Word (QS.ScalarGen ⊎ QS.Gen n)) →
               G._≈_ ⟦ w ⟧ ((sw w • Ev.scal (gw w)) • ε , ε • gw w)
    ⟦⟧-split w = sound (split w) ⟨G⟩ val (sw w) (gw w)

  ----------------------------------------------------------------------
  -- The correction carried by a quotient derivation
  --
  -- Extension.corr-witness, with the conjugations dropped.  Only the
  -- axiom case has content — it is the twisted relator — while sym
  -- inverts in the kernel, trans concatenates and cong concatenates
  -- after crossing the middle gate word, which is centrality again.

  private
    corr-witness : {a b : QS.Circuit n} → QB._≈_ a b →
                   ∃ λ (w : Word QS.ScalarGen) →
                     EB._≈_ [ a ]ᵣ ([ w ]ₗ • [ b ]ᵣ)
    corr-witness QB.refl = ε , EB.sym EB.left-unit
    corr-witness (QB.sym p) with corr-witness p
    ... | wp , pp = GS._⁻¹ wp ,
      EB.trans (EB.sym EB.left-unit)
        (EB.trans (EB.cong (EB.sym (lefts GS.inverseˡ)) EB.refl)
          (EB.trans EB.assoc (EB.cong EB.refl (EB.sym pp))))
    corr-witness (QB.trans p q) with corr-witness p | corr-witness q
    ... | wp , pp | wq , pq = wp • wq ,
      EB.trans pp (EB.trans (EB.cong EB.refl pq) (EB.sym EB.assoc))
    corr-witness (QB.cong {a} {b} {a'} {b'} p q)
      with corr-witness p | corr-witness q
    ... | wp , pp | wq , pq = wp • wq ,
      EB.trans (EB.cong pp pq)
        (EB.trans EB.assoc
          (EB.trans (EB.cong EB.refl (EB.sym EB.assoc))
            (EB.trans (EB.cong EB.refl (EB.cong (central b wq) EB.refl))
              (EB.trans (EB.cong EB.refl EB.assoc) (EB.sym EB.assoc)))))
    corr-witness QB.assoc      = ε , EB.trans EB.assoc (EB.sym EB.left-unit)
    corr-witness QB.left-unit  = ε , EB.refl
    corr-witness QB.right-unit =
      ε , EB.trans EB.right-unit (EB.sym EB.left-unit)
    corr-witness (QB.axiom r)  = QS.corr r , EB.axiom (mid (right (tw r)))

    corrOf : {a b : QS.Circuit n} → QB._≈_ a b → Word QS.ScalarGen
    corrOf p = proj₁ (corr-witness p)

    corrOf-eq : {a b : QS.Circuit n} (p : QB._≈_ a b) →
                EB._≈_ [ a ]ᵣ ([ corrOf p ]ₗ • [ b ]ᵣ)
    corrOf-eq p = proj₂ (corr-witness p)

    -- ... and it is the scalar defect the cocycle accumulates.  No
    -- second induction: the equation above is pushed through soundness,
    -- and it is there that `real` is spent.
    scal-corr : {a b : QS.Circuit n} (p : QB._≈_ a b) →
                KB._≈_ (Ev.scal a) (corrOf p • Ev.scal b)
    scal-corr {a} {b} p =
      KB.trans (KB.refl' (Eq.cong proj₁ (Eq.sym (emb-r a))))
        (KB.trans (proj₁ chain) KB.right-unit)
      where
      chain : G._≈_ ⟦ [ a ]ᵣ ⟧ ((corrOf p • Ev.scal b) • ε , ε • b)
      chain = sound (corrOf-eq p) ⟨G⟩ val (corrOf p) b

  ----------------------------------------------------------------------
  -- Completeness
  --
  -- Two words with the same denotation split into scalar and gate parts
  -- whose gate parts agree in the quotient; the correction of that
  -- agreement is exactly the difference of the scalar parts, and
  -- cancelling it in the kernel puts the two split forms on top of one
  -- another.

  injective : ∀ {w v} → G._≈_ ⟦ w ⟧ ⟦ v ⟧ → EB._≈_ w v
  injective {w} {v} e =
    EB.trans (split w)
      (EB.trans (EB.cong EB.refl (corrOf-eq pg))
        (EB.trans (EB.sym EB.assoc)
          (EB.trans (EB.cong (lefts sw•k≈sw') EB.refl) (EB.sym (split v)))))
    where
    eq : G._≈_ ((sw w • Ev.scal (gw w)) • ε , ε • gw w)
               ((sw v • Ev.scal (gw v)) • ε , ε • gw v)
    eq = G-sym (⟦⟧-split w) ⟨G⟩ e ⟨G⟩ ⟦⟧-split v

    pg : QB._≈_ (gw w) (gw v)
    pg = QB.trans (QB.sym QB.left-unit) (QB.trans (proj₂ eq) QB.left-unit)

    es : KB._≈_ (sw w • Ev.scal (gw w)) (sw v • Ev.scal (gw v))
    es = KB.trans (KB.sym KB.right-unit) (KB.trans (proj₁ eq) KB.right-unit)

    sw•k≈sw' : KB._≈_ (sw w • corrOf pg) (sw v)
    sw•k≈sw' = GS.•-cancelʳ
      (KB.trans KB.assoc
        (KB.trans (KB.cong KB.refl (KB.sym (scal-corr pg))) es))

  ----------------------------------------------------------------------
  -- Surjectivity
  --
  -- The splitting read backwards: a pair (a , b) is the value of
  -- [ a · defect(b)⁻¹ ]ₗ • [ b ]ᵣ, the scalar corrected by the inverse of
  -- what the gate word itself picks up.

  surjective : Surjective EB._≈_ G._≈_ ⟦_⟧
  surjective (a , b) =
    [ a • GS._⁻¹ (Ev.scal b) ]ₗ • [ b ]ᵣ , λ z≈ → sound z≈ ⟨G⟩ claim
    where
    claim : G._≈_ ⟦ [ a • GS._⁻¹ (Ev.scal b) ]ₗ • [ b ]ᵣ ⟧ (a , b)
    claim = val (a • GS._⁻¹ (Ev.scal b)) b ⟨G⟩ (first , QB.left-unit)
      where
      first : KB._≈_ (((a • GS._⁻¹ (Ev.scal b)) • Ev.scal b) • ε) a
      first =
        KB.trans KB.right-unit
          (KB.trans KB.assoc
            (KB.trans (KB.cong KB.refl GS.inverseˡ) KB.right-unit))

  ----------------------------------------------------------------------
  -- Grouplikeness of the exact alphabet
  --
  -- A scalar generator inverts in the cyclic factor and the inverse
  -- embeds; a gate inverts in the Paper-V0 factor, but that inversion is
  -- a quotient derivation, so it reaches the extension only up to its
  -- correction — which the scalar prefix cancels.

  grouplike : Grouplike Γ
  grouplike (inj₁ x) = [ proj₁ (glS x) ]ₗ , lefts (proj₂ (glS x))
  grouplike (inj₂ y) =
    [ GS._⁻¹ (corrOf (proj₂ (glQ y))) ]ₗ • [ proj₁ (glQ y) ]ᵣ ,
    EB.trans EB.assoc
      (EB.trans
        (EB.cong EB.refl
          (EB.trans (corrOf-eq (proj₂ (glQ y))) EB.right-unit))
        (lefts GS.inverseˡ))

  ----------------------------------------------------------------------
  -- The presentation
  --
  -- As a monoid presentation first: ⟦_⟧ preserves • and ε on the nose,
  -- the product of the central extension being pairing with a twist in
  -- the first component only.  Grouplikeness promotes it.

  monoid-presentation : Γ IsMonoidPresentationOf (Group.monoid G)
  monoid-presentation = record
    { ⟦_⟧ = ⟦_⟧
    ; iso = record
      { isMonoidMonomorphism = record
        { isMonoidHomomorphism = IC.isMonoidHomomorphism
        ; injective            = injective
        }
      ; surjective = surjective
      }
    }

  presentation : Γ IsPresentationOf G
  presentation =
    monoidPresentation⇒presentation {G = G} monoid-presentation grouplike

------------------------------------------------------------------------
-- The theorem
--
-- The exact qupit Clifford rule set — the scalar ω, its order, its
-- centrality, and the sixteen Paper-V0 relations with their corrections
-- — presents the central extension of the mod-scalar group by the
-- scalars, at every width, for every generator data whose cocycle
-- realises those corrections.

presentation : ∀ (n : ℕ) (gd : PE.GeneratorData n) → PE.Realises n gd →
               (QS._Exact,_===_ n) IsPresentationOf (PE.Presented-group n gd)
presentation n gd real = Exact-Presentation.presentation n gd real

------------------------------------------------------------------------
-- ... with the generator data discharged
--
-- Of the two inputs above only one is an assumption.  The generator
-- data — which is what the cocycle, hence the group itself, is built
-- from — is supplied at every width by SemFE, by pulling the Weyl
-- cocycle of Clifford.Qupit.Semantics back along Paper-V0's
-- presentation; it needs no hypothesis.
--
-- What is left is Realises alone: that the corrections that cocycle
-- accumulates are the ones `corr` records.  It is not free — the split
-- cocycle is a cocycle too, and Semantics.split-forces shows it cannot
-- realise corr — and it is the qupit analogue of Selinger's scalar
-- kernel: for each of the sixteen Paper-V0 relations, the ½·sform
-- accumulated along the two sides must differ by exactly corr, which is
-- ε for fifteen of them and ω^((p² - 1)/8) for order-SH.

exact-generator-data : ∀ (n : ℕ) → PE.GeneratorData n
exact-generator-data = FE.generator-data

presentation-n : ∀ (n : ℕ) → PE.Realises n (exact-generator-data n) →
                 (QS._Exact,_===_ n) IsPresentationOf
                   (PE.Presented-group n (exact-generator-data n))
presentation-n n = presentation n (exact-generator-data n)

------------------------------------------------------------------------
-- ... and with the last hypothesis reduced to arithmetic
--
-- SemRealises shows that with this cocycle the scalar a circuit picks up
-- is ω ^ Φ, for an explicit Φ : Circuit n → ℤ/pℤ, so Realises follows
-- from nineteen equations in ℤ/pℤ — one per Paper-V0 rule and one per
-- structural rule — with no words, no cocycle and no extension in them.
-- That is the sharpest form the remaining obligation takes.

presentation-Φ : ∀ (n : ℕ) → RL.Width.Φ-Corr n →
                 (QS._Exact,_===_ n) IsPresentationOf
                   (PE.Presented-group n (exact-generator-data n))
presentation-Φ n hyp = presentation-n n (RL.realises n hyp)

------------------------------------------------------------------------
-- ... and with the structural rules discharged
--
-- Φ-Corr is an induction over the relation, and its cong↑ case is a
-- theorem: shifting a circuit up a wire leaves its phase alone
-- (SemShift's shift lemma, whence SemRealises.Φ-↑).  Peeling it off
-- leaves the sixteen Paper-V0 rules (SRel-Φ) and the two commutation
-- rules (Comm-Φ), at every width — of which the six S-free ones are
-- already proved in SemRealises.Rules₂ and Rules₃.

presentation-rules : RL.SRel-Φ → RL.Comm-Φ → ∀ (n : ℕ) →
                     (QS._Exact,_===_ n) IsPresentationOf
                       (PE.Presented-group n (exact-generator-data n))
presentation-rules sr cm n = presentation-n n (RL.realises-from sr cm n)

------------------------------------------------------------------------
-- ... and with ALL THREE structural rules discharged
--
-- cong↑ is Φ-↑ (SemShift's shift lemma), and comm₁ / comm₂ are
-- SemRealises.comm-Φ: the shifted circuit's Pauli lives above wire 0
-- and the bottom gate's lives on it, so both cocycle terms vanish —
-- sform pairing a trivial side against a non-trivial one at every wire.
--
-- What is left is the SIXTEEN Paper-V0 rules and nothing else, as
-- sixteen equations in ℤ/pℤ.  Six of them (the S-free ones) are already
-- proved in SemRealises.Rules₂ and Rules₃.

presentation-srel : RL.SRel-Φ → ∀ (n : ℕ) →
                    (QS._Exact,_===_ n) IsPresentationOf
                      (PE.Presented-group n (exact-generator-data n))
presentation-srel sr n = presentation-n n (RL.realises-srel sr n)

------------------------------------------------------------------------
-- ... and with nothing left
--
-- SemSRel proves those sixteen equations, so `Realises` is discharged
-- and the theorem holds outright.  Ten of the sixteen are Pauli
-- arithmetic in SemRealises itself; of the rest, three are the
-- multiplier rules, which vanish because R = S·Z^½ has no Pauli
-- (SemLocal), one is blake-c12, which vanishes because every Pauli in
-- it is pure-Z (SemZBlock), and one is order-SH, whose phase is -⅛ —
-- the residue of (p² - 1)/8, which is what `corr` assigns it
-- (SemLocal's has-SH3, with SemSHExp for the arithmetic).
--
-- So: at every width, over every primitive root, the exact qupit
-- Clifford rule set presents the central extension of the mod-scalar
-- group by the scalars, on no hypothesis at all.

presentation-exact : ∀ (n : ℕ) →
                     (QS._Exact,_===_ n) IsPresentationOf
                       (PE.Presented-group n (exact-generator-data n))
presentation-exact n = presentation-n n (SR.realises n)
