------------------------------------------------------------------------
-- Presentations of groups
--
-- Presentations of group extensions (Proposition 2.55).
--
-- A group G with a normal subgroup N is an extension of N by G/N.
-- Given a presentation ⟨Y | S⟩ of N and a presentation ⟨X̄ | R̄⟩ of the
-- quotient G/N, a presentation of G on the generators X ∪ Y is obtained
-- from three families of relations:
--
--   S : the relations of N,                        (on Y)
--   T : x⁻¹ y x = w_{x y}  for x ∈ X, y ∈ Y,        (conjugation)
--   R : r = w_r            for each relator r̄ ∈ R̄,  (twisted relators)
--
-- where, choosing coset representatives x ∈ G with xN = x̄, the words
-- w_{x y}, w_r ∈ (Y ∪ Y⁻¹)* record — inside G — the values of the
-- conjugate x⁻¹ y x ∈ N and of the lift r ∈ N of each quotient relator.
--
-- This is the general (possibly non-split) analogue of the semi-direct
-- product in Presentation.Construct.Properties.SemiDirectProduct: the
-- split case is exactly the one in which every correction word w_r is
-- trivial, so that the quotient relations R̄ hold on the nose on the
-- representatives (the trivial correction `no-twist` below).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.Construct.Properties.Extension where

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Word.Base
open import Presentation.Construct.Base

private
  variable
    N X : Set

------------------------------------------------------------------------
-- The twisted quotient relators R
--
-- In the framework a relation is a pair `u === v`, corresponding to the
-- relator `u v⁻¹`.  Lifting a quotient relation `ū === v̄` (a pair of
-- words over the representatives X) to G leaves a discrepancy in N: the
-- two lifts differ by a correction word `corr r̄ ∈ (Y ∪ Y⁻¹)*`.  The
-- twisted relation records this as
--
--     [ ū ]ᵣ  ===  [ corr r̄ ]ₗ • [ v̄ ]ᵣ.
--
-- The relator form `r =_G w_r` of Proposition 2.55 is the special case
-- v̄ = ε (then `[ ū ]ᵣ === [ corr r̄ ]ₗ`).

data RelTwist (R̄ : WRel X) (corr : ∀ {u v} → R̄ u v → Word N)
    : WRel (N ⊎ X) where
  tw : ∀ {u v} (r̄ : R̄ u v) →
       RelTwist R̄ corr [ u ]ᵣ ([ corr r̄ ]ₗ • [ v ]ᵣ)

------------------------------------------------------------------------
-- The extension presentation  ⟨ X ∪ Y | R ∪ S ∪ T ⟩
--
-- N (= Y) is the left factor and carries its own relations S; X are the
-- coset representatives and carry no relations of their own (EmptyRel),
-- since every quotient relation is twisted into the mixed part.  The
-- mixed relation is the union of the conjugation relation T (ConjRelʷ)
-- and the twisted relators R (RelTwist).

extension-presentation :
  (S : WRel N) (R̄ : WRel X)
  (conj : X → N → Word N) (corr : ∀ {u v} → R̄ u v → Word N) →
  WRel (N ⊎ X)
extension-presentation S R̄ conj corr =
  S ⋄ EmptyRel ⋄ (ConjRelʷ conj ∪ RelTwist R̄ corr)

------------------------------------------------------------------------
-- Split extensions
--
-- The extension splits when a set of coset representatives can be chosen
-- forming a complement C ≅ G/N.  Then the lifts of the quotient relators
-- already vanish in G, i.e. every correction word is trivial.  With the
-- trivial correction the twisted relators degenerate to pure right-hand
-- relations, and the extension presentation is the semi-direct product
--    S ⋄ R̄ ⋄ ConjRelʷ conj
-- studied in Presentation.Construct.Properties.SemiDirectProduct.

no-twist : ∀ {R̄ : WRel X} {u v} → R̄ u v → Word N
no-twist {u = u} _ = ε

------------------------------------------------------------------------
-- Proposition 2.55
--
-- With the notation above, ⟨ X ∪ Y | R ∪ S ∪ T ⟩ is a presentation of G.
--
-- We state the proposition inside the framework's `_IsPresentationOf_`.
-- The interpretation ⟦_⟧₀ sends each generator to its value in G (an
-- element of N for y ∈ Y, a chosen coset representative for x ∈ X), and
-- `sound-ax` is the compatibility asserting that conj and corr really do
-- record the conjugates and relator-lifts computed in G — this is the
-- content of "G is an extension realising the recipe".  The proof
-- extends the Reidemeister–Schreier coset enumeration of the semi-direct
-- product (SemiDirectProduct) so that closing a twisted relator emits
-- its correction word; it is the remaining goal.

module _ {N X : Set}
  (S : WRel N) (R̄ : WRel X)
  (conj : X → N → Word N) (corr : ∀ {u v} → R̄ u v → Word N)
  where

  open import Algebra.Bundles using (Group)
  open import Algebra.Construct.Sub.Group
  open import Level using (0ℓ)
  open import Presentation.Definitions using (_IsPresentationOf_)
  open import ForStdlib.Algebra.Construct.Extension
  open import Normalization.NormalForm.Propositional
    using (NormalForm ; BijectiveNormalForm)

  ext : WRel (N ⊎ X)
  ext = extension-presentation S R̄ conj corr

  extp = (ConjRelʷ conj ∪ RelTwist R̄ corr)

  module Presentation
    (GN : Group 0ℓ 0ℓ)
    (GQ : Group 0ℓ 0ℓ)
    (et : Extension GN GQ)
    (let G = Extension.total et)
    (pN : S IsPresentationOf GN)
    (pQ : R̄ IsPresentationOf GQ)
    (⟦_⟧₀ : (N ⊎ X) → Group.Carrier G)
    -- The syntactic reduction data: normal forms for the two factors.
    -- NFQ (canonical quotient cosets) is the coset index; NFS carries
    -- the N-part of the extension's normal form.
    {NFS NFQ : Set}
    (nfpS : BijectiveNormalForm S NFS)
    (nfpQ : BijectiveNormalForm R̄ NFQ)
    where

    open import Normalization.StarInterp ext
    module E = Extend (Group.monoid G) ⟦_⟧₀

    -- The monoid-homomorphic reading of a word in G.
    ⟦_⟧ : Word (N ⊎ X) → Group.Carrier G
    ⟦_⟧ = E.⟦_⟧

    open import Algebra.Morphism.Structures
      using (module MonoidMorphisms ; module GroupMorphisms)
    open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
    open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
    open import Presentation.Definitions
      using (_IsSubPresentationOf_ ; isPresentationOf)
    open import Function.Definitions using (Surjective)
    import Normalization.StarPresentation
    import Presentation.Base as PB

    private
      module Gm  = Group G
      module GNm = Group GN
      module PN  = _IsPresentationOf_ pN

    -- The inclusion N ↪ G and its homomorphism laws.
    incl : GNm.Carrier → Gm.Carrier
    incl = Extension.incl et

    private
      module ιG = GroupMorphisms (Group.rawGroup GN) (Group.rawGroup G)
      incl-cong = ιG.IsGroupHomomorphism.⟦⟧-cong (Extension.incl-homo et)
      incl-∙    = ιG.IsGroupHomomorphism.homo    (Extension.incl-homo et)
      incl-ε    = ιG.IsGroupHomomorphism.ε-homo  (Extension.incl-homo et)

    -- The N-presentation interpretation ⟦_⟧N : Word N → N and its laws.
    ⟦_⟧N : Word N → GNm.Carrier
    ⟦_⟧N = PN.⟦_⟧

    private
      module πG = GroupMorphisms (Group.rawGroup PN.GL.•-ε-group)
                                 (Group.rawGroup GN)
      PN-hom  = πG.IsGroupMonomorphism.isGroupHomomorphism
                  (πG.IsGroupIsomorphism.isGroupMonomorphism PN.iso)
      PN-cong = πG.IsGroupHomomorphism.⟦⟧-cong PN-hom
      PN-∙    = πG.IsGroupHomomorphism.homo    PN-hom
      PN-ε    = πG.IsGroupHomomorphism.ε-homo  PN-hom
      PN-surj = πG.IsGroupIsomorphism.surjective PN.iso

    -- The quotient interpretation ⟦_⟧Q : Word X → GQ and its laws.
    private
      module GQm = Group GQ
      module PQi = _IsPresentationOf_ pQ
    ⟦_⟧Q : Word X → GQm.Carrier
    ⟦_⟧Q = PQi.⟦_⟧
    private
      module ρG = GroupMorphisms (Group.rawGroup PQi.GL.•-ε-group)
                                 (Group.rawGroup GQ)
      PQ-mono = ρG.IsGroupIsomorphism.isGroupMonomorphism PQi.iso
      PQ-hom  = ρG.IsGroupMonomorphism.isGroupHomomorphism PQ-mono
      PQ-∙    = ρG.IsGroupHomomorphism.homo    PQ-hom
      PQ-ε    = ρG.IsGroupHomomorphism.ε-homo  PQ-hom
      PQ-inj  = ρG.IsGroupMonomorphism.injective PQ-mono
      PQ-surj = ρG.IsGroupIsomorphism.surjective PQi.iso

    -- The projection G ↠ GQ and its homomorphism laws.
    proj : Gm.Carrier → GQm.Carrier
    proj = Extension.proj et
    private
      module πp = GroupMorphisms (Group.rawGroup G) (Group.rawGroup GQ)
      proj-∙ = πp.IsGroupHomomorphism.homo   (Extension.proj-homo et)
      proj-ε = πp.IsGroupHomomorphism.ε-homo (Extension.proj-homo et)

    -- The realisation condition: ⟦_⟧₀ sends each N-generator to the image
    -- under incl of its N-value.  This is what makes ⟦_⟧₀ interpret the
    -- Y-part of the presentation inside the normal subgroup N ≤ G.
    Realises : Set
    Realises = ∀ n → Gm._≈_ ⟦ inj₁ n ⟧₀ (incl ⟦ [ n ]ʷ ⟧N)

    -- A left-embedded word is read, in G, as the incl-image of its
    -- N-value: ⟦ [ w ]ₗ ⟧ ≈ incl ⟦ w ⟧N.
    emb-l : Realises → ∀ w → Gm._≈_ ⟦ [ w ]ₗ ⟧ (incl ⟦ w ⟧N)
    emb-l real [ n ]ʷ = real n
    emb-l real ε      = Gm.sym (Gm.trans (incl-cong PN-ε) incl-ε)
    emb-l real (w • v) =
      Gm.trans (Gm.∙-cong (emb-l real w) (emb-l real v))
        (Gm.trans (Gm.sym (incl-∙ ⟦ w ⟧N ⟦ v ⟧N))
                  (incl-cong (GNm.sym (PN-∙ w v))))

    -- sound-s transforms soundness of S (i.e. pN, which presents N) into
    -- soundness of the S-axioms with respect to the ambient group G.
    sound-s : Realises → ∀ {w v} → S w v → Gm._≈_ ⟦ [ w ]ₗ ⟧ ⟦ [ v ]ₗ ⟧
    sound-s real {w} {v} x =
      Gm.trans (emb-l real w)
        (Gm.trans (incl-cong (PN-cong (PB._≈_.axiom x)))
                  (Gm.sym (emb-l real v)))

    -- sound-t transforms soundness of extp (the mixed relations R ∪ T)
    -- into soundness of the whole extension relation ext = S ⋄ ∅ ⋄ extp,
    -- given soundness of the S-axioms (typically sound-s real).  The
    -- right factor EmptyRel contributes no axioms.
    sound-t : (∀ {w v} → S w v → Gm._≈_ ⟦ [ w ]ₗ ⟧ ⟦ [ v ]ₗ ⟧)
            → (∀ {w v} → extp w v → Gm._≈_ ⟦ w ⟧ ⟦ v ⟧)
            → ∀ {w v} → ext w v → Gm._≈_ ⟦ w ⟧ ⟦ v ⟧
    sound-t sS sT (left x)  = sS x
    sound-t sS sT (right ())
    sound-t sS sT (mid x)   = sT x

    ------------------------------------------------------------------
    -- The twist mechanism
    --
    -- corr is given per R̄-axiom; a whole R̄-derivation a ≈q b carries an
    -- accumulated correction word in N such that, right-embedded into ext,
    --     [ a ]ᵣ  ≈  [ correction ]ₗ • [ b ]ᵣ.
    -- The correction is built by recursion on the derivation: axioms
    -- contribute corr, transitivity concatenates, congruence conjugates
    -- the second correction past the first factor (the T-relation), and
    -- symmetry inverts (via S's group-likeness).  This is exactly the data
    -- the coset action needs to emit when a rep word is reduced modulo R̄.

    conjs : X → Word N → Word N
    conjs = conj ⁿ'
    conjss : Word X → Word N → Word N
    conjss = conj ʰ'

    open PB ext using () renaming (_≈_ to _≈ₑ_)
    open PB R̄  using () renaming (_≈_ to _≈q_)
    open PB S  using () renaming (_≈_ to _≈s_ ; refl' to refl'ₛ)
    open Group-Lemmas S PN.gl using ()
      renaming (_⁻¹ to _⁻¹ₛ ; inverseˡ to inverseˡₛ)
    open LeftRightCongruence S EmptyRel extp using (lefts)

    -- Moving a rep letter x rightward past an N-word emits its conjugate
    -- (the T = ConjRelʷ axiom, the left summand of extp).
    lemma-comm1 : ∀ x w → [ [ x ]ʷ ]ᵣ • [ w ]ₗ ≈ₑ [ conjs x w ]ₗ • [ [ x ]ʷ ]ᵣ
    lemma-comm1 x [ n ]ʷ = _≈ₑ_.axiom (mid (left (comm n x)))
    lemma-comm1 x ε = _≈ₑ_.trans _≈ₑ_.right-unit (_≈ₑ_.sym _≈ₑ_.left-unit)
    lemma-comm1 x (w • w₁) with lemma-comm1 x w | lemma-comm1 x w₁
    ... | ih1 | ih2 =
      _≈ₑ_.trans (_≈ₑ_.sym _≈ₑ_.assoc)
        (_≈ₑ_.trans (_≈ₑ_.cong ih1 _≈ₑ_.refl)
          (_≈ₑ_.trans _≈ₑ_.assoc
            (_≈ₑ_.trans (_≈ₑ_.cong _≈ₑ_.refl ih2) (_≈ₑ_.sym _≈ₑ_.assoc))))

    lemma-comm : ∀ w v → [ v ]ᵣ • [ w ]ₗ ≈ₑ [ conjss v w ]ₗ • [ v ]ᵣ
    lemma-comm w [ x ]ʷ = lemma-comm1 x w
    lemma-comm w ε = _≈ₑ_.trans _≈ₑ_.left-unit (_≈ₑ_.sym _≈ₑ_.right-unit)
    lemma-comm w (v • v₁) with lemma-comm w v₁ | lemma-comm (conjss v₁ w) v
    ... | ih2 | ih1 =
      _≈ₑ_.sym
        (_≈ₑ_.trans (_≈ₑ_.sym _≈ₑ_.assoc)
          (_≈ₑ_.trans (_≈ₑ_.cong (_≈ₑ_.sym ih1) _≈ₑ_.refl)
            (_≈ₑ_.trans _≈ₑ_.assoc
              (_≈ₑ_.trans (_≈ₑ_.cong _≈ₑ_.refl (_≈ₑ_.sym ih2)) (_≈ₑ_.sym _≈ₑ_.assoc)))))

    -- The correction carried by an R̄-derivation, with its ext-proof.
    corr-witness : ∀ {a b} → a ≈q b →
      ∃ λ (w : Word N) → [ a ]ᵣ ≈ₑ [ w ]ₗ • [ b ]ᵣ
    corr-witness _≈q_.refl        = ε , _≈ₑ_.sym _≈ₑ_.left-unit
    corr-witness (_≈q_.sym {a} {b} p) with corr-witness p
    ... | wp , pp = (wp ⁻¹ₛ) ,
      _≈ₑ_.trans (_≈ₑ_.sym _≈ₑ_.left-unit)
        (_≈ₑ_.trans (_≈ₑ_.cong (_≈ₑ_.sym (lefts inverseˡₛ)) _≈ₑ_.refl)
          (_≈ₑ_.trans _≈ₑ_.assoc (_≈ₑ_.cong _≈ₑ_.refl (_≈ₑ_.sym pp))))
    corr-witness (_≈q_.trans p q) with corr-witness p | corr-witness q
    ... | wp , pp | wq , pq = (wp • wq) ,
      _≈ₑ_.trans pp (_≈ₑ_.trans (_≈ₑ_.cong _≈ₑ_.refl pq) (_≈ₑ_.sym _≈ₑ_.assoc))
    corr-witness (_≈q_.cong {a} {b} {a'} {b'} p q)
      with corr-witness p | corr-witness q
    ... | wp , pp | wq , pq = (wp • conjss b wq) ,
      _≈ₑ_.trans (_≈ₑ_.cong pp pq)
        (_≈ₑ_.trans _≈ₑ_.assoc
          (_≈ₑ_.trans (_≈ₑ_.cong _≈ₑ_.refl (_≈ₑ_.sym _≈ₑ_.assoc))
            (_≈ₑ_.trans (_≈ₑ_.cong _≈ₑ_.refl (_≈ₑ_.cong (lemma-comm wq b) _≈ₑ_.refl))
              (_≈ₑ_.trans (_≈ₑ_.cong _≈ₑ_.refl _≈ₑ_.assoc) (_≈ₑ_.sym _≈ₑ_.assoc)))))
    corr-witness _≈q_.assoc      =
      ε , _≈ₑ_.trans _≈ₑ_.assoc (_≈ₑ_.sym _≈ₑ_.left-unit)
    corr-witness _≈q_.left-unit  = ε , _≈ₑ_.refl
    corr-witness _≈q_.right-unit =
      ε , _≈ₑ_.trans _≈ₑ_.right-unit (_≈ₑ_.sym _≈ₑ_.left-unit)
    corr-witness (_≈q_.axiom r̄)  = corr r̄ , _≈ₑ_.axiom (mid (right (tw r̄)))

    -- The correction word, and its defining ext-equation.
    corrOf : ∀ {a b} → a ≈q b → Word N
    corrOf p = proj₁ (corr-witness p)

    corrOf-eq : ∀ {a b} (p : a ≈q b) → [ a ]ᵣ ≈ₑ [ corrOf p ]ₗ • [ b ]ᵣ
    corrOf-eq p = proj₂ (corr-witness p)

    ------------------------------------------------------------------
    -- The correction-free part of the quotient relation
    --
    -- Reading corr-witness backwards: of the eight ways to build an
    -- R̄-derivation only `axiom` contributes anything, since refl, assoc
    -- and the two unit laws give ε while trans concatenates, cong
    -- conjugates and sym inverts.  So the accumulated correction is
    -- trivial as soon as every axiom the derivation uses is.
    --
    -- That is a property of a derivation, and a derivation is opaque —
    -- one cannot ask an arbitrary p : a ≈q b which axioms it used.  The
    -- fix is to name the correction-free axioms as a relation in their
    -- own right and work in the congruence THEY generate: Corr-free is
    -- the sub-relation of R̄ carrying, with each axiom, the proof that it
    -- lifts exactly.  A Corr-free derivation is then by construction one
    -- whose corrections all vanish, and rights₀ below says such a
    -- derivation crosses into the extension with nothing left behind.
    --
    -- Note this is exactly the extra strength the right embedding lacks
    -- in general: the right factor of ext carries EmptyRel, so
    -- LeftRightCongruence.rights transports the monoid laws and nothing
    -- else, and a genuine quotient axiom can only enter through tw.

    -- The side condition is propositional equality, not just ≈s: it
    -- costs nothing (corr reduces on the nose for every axiom that lifts
    -- exactly, so witnesses are refl) and it is what lets a client
    -- transport a correction-free axiom along a structural rule.  If
    -- corr r̄ is ε literally, so is any f (corr r̄) with f ε = ε — which
    -- is how a wire-shift rule keeps its axioms correction-free.
    open import Relation.Binary.PropositionalEquality using (_≡_)

    Corr-free : WRel X
    Corr-free u v = ∃ λ (r̄ : R̄ u v) → corr r̄ ≡ ε

    open PB Corr-free using () renaming (_≈_ to _≈₀_)

    -- The right embedding is a congruence for the correction-free part.
    -- Only the axiom case has content: tw emits the correction, and the
    -- axiom's own triviality proof cancels it against left-unit.
    rights₀ : ∀ {a b} → a ≈₀ b → [ a ]ᵣ ≈ₑ [ b ]ᵣ
    rights₀ _≈₀_.refl          = _≈ₑ_.refl
    rights₀ (_≈₀_.sym p)       = _≈ₑ_.sym (rights₀ p)
    rights₀ (_≈₀_.trans p q)   = _≈ₑ_.trans (rights₀ p) (rights₀ q)
    rights₀ (_≈₀_.cong p q)    = _≈ₑ_.cong (rights₀ p) (rights₀ q)
    rights₀ _≈₀_.assoc         = _≈ₑ_.assoc
    rights₀ _≈₀_.left-unit     = _≈ₑ_.left-unit
    rights₀ _≈₀_.right-unit    = _≈ₑ_.right-unit
    rights₀ (_≈₀_.axiom (r̄ , triv)) =
      _≈ₑ_.trans (_≈ₑ_.axiom (mid (right (tw r̄))))
        (_≈ₑ_.trans (_≈ₑ_.cong (lefts (refl'ₛ triv)) _≈ₑ_.refl)
                    _≈ₑ_.left-unit)

    ------------------------------------------------------------------
    -- The twisted coset table
    --
    -- Cosets are the canonical quotient representatives NFQ (the normal
    -- form for R̄): unique, hence a discrete index — which is what lets
    -- the reduced coset action satisfy h-wd-ax while keeping congruence
    -- trivial.  Advancing a coset by a quotient generator x reduces the
    -- representative back to canonical form and emits the correction of
    -- that reduction; advancing by an N-generator conjugates it past the
    -- representative and keeps the coset.

    import Normalization.NormalForm.Setoid as SNF
    import Normalization.NormalForm.Uniqueness as NFU
    import Normalization.CosetNF as CNF
    open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
    import Data.Product.Relation.Binary.Pointwise.NonDependent as PW

    private
      module NQ = SNF.BijectiveNormalForm nfpQ
      module NS = SNF.BijectiveNormalForm nfpS

    -- The bijection gives both directions: inv-nf∘nf ≈ id and nf∘inv-nf ≡ id.
    nf∘inv : ∀ c → NQ.nf (NQ.inv-nf c) ≡ c
    nf∘inv c = proj₂ (NQ.surjective c) _≈q_.refl

    nf∘invS : ∀ a → NS.nf (NS.inv-nf a) ≡ a
    nf∘invS a = proj₂ (NS.surjective a) _≈s_.refl

    -- Coset index: the canonical quotient normal forms (unique reps).
    Cᶜ : Set
    Cᶜ = NFQ

    -- Canonical representative of a coset.
    rep : Cᶜ → Word X
    rep = NQ.inv-nf

    -- The identity coset.
    Iᶜ : Cᶜ
    Iᶜ = NQ.nf ε

    -- The generator embedding N ↪ ext and the Schreier section.
    fᶜ : N → Word (N ⊎ X)
    fᶜ n = [ inj₁ n ]ʷ

    secᶜ : Cᶜ → Word (N ⊎ X)
    secᶜ c = [ rep c ]ᵣ

    -- The coset action: an N-generator conjugates past the representative
    -- and keeps the coset; a quotient generator advances the coset to the
    -- reduced representative and emits the correction of that reduction.
    hᶜ : Cᶜ → (N ⊎ X) → Word N × Cᶜ
    hᶜ c (inj₁ n) = conjss (rep c) [ n ]ʷ , c
    hᶜ c (inj₂ x) =
      corrOf (_≈q_.sym (NQ.inv-nf∘nf=id {rep c • [ x ]ʷ})) ,
      NQ.nf (rep c • [ x ]ʷ)

    -- The single-level coset extension carrying the twisted table.
    module CT = CNF.SingleLevel S ext Cᶜ Iᶜ fᶜ hᶜ secᶜ

    ------------------------------------------------------------------
    -- Well-definedness of the coset action (h-wd-ax)

    -- Structural laws of the word-valued conjugation.
    conjss-c-ε=ε : ∀ c → conjss c ε ≡ ε
    conjss-c-ε=ε [ x ]ʷ  = Eq.refl
    conjss-c-ε=ε ε       = Eq.refl
    conjss-c-ε=ε (c • c₁) with conjss-c-ε=ε c₁
    ... | ih rewrite ih = conjss-c-ε=ε c

    conjss-homo : ∀ c w v → conjss c (w • v) ≡ conjss c w • conjss c v
    conjss-homo [ x ]ʷ  w v = Eq.refl
    conjss-homo ε       w v = Eq.refl
    conjss-homo (c • c₁) w v with conjss-homo c₁ w v
    ... | ih with conjss-homo c (conjss c₁ w) (conjss c₁ v)
    ... | ih2 rewrite ih = ih2

    -- Threading hᶜ through a left-embedded word keeps the coset fixed and
    -- conjugates by the representative.
    lemma-hᶜ-left : ∀ c a → (hᶜ ᵗ) c [ a ]ₗ ≡ (conjss (rep c) a , c)
    lemma-hᶜ-left c [ n ]ʷ = Eq.refl
    lemma-hᶜ-left c ε =
      PW.≡×≡⇒≡ (Eq.sym (conjss-c-ε=ε (rep c)) , Eq.refl)
    lemma-hᶜ-left c (a • a₁)
      rewrite lemma-hᶜ-left c a | lemma-hᶜ-left c a₁ =
      PW.≡×≡⇒≡ (Eq.sym (conjss-homo (rep c) a a₁) , Eq.refl)

    -- (fᶜ ʷ) is the left embedding.
    aux-fᶜ : ∀ w → (fᶜ ʷ) w ≡ [ w ]ₗ
    aux-fᶜ [ n ]ʷ = Eq.refl
    aux-fᶜ ε = Eq.refl
    aux-fᶜ (w • v) rewrite aux-fᶜ w | aux-fᶜ v = Eq.refl

    -- RS hypothesis (3): fᶜ respects the relations of S.
    f-wd-ax : ∀ {w v} → S w v → (fᶜ ʷ) w ≈ₑ (fᶜ ʷ) v
    f-wd-ax {w} {v} x rewrite aux-fᶜ w | aux-fᶜ v = lefts (_≈s_.axiom x)

    -- RS hypothesis (5): section/action compatibility.  The N-generator
    -- case is the conjugation move lemma-comm; the quotient-generator case
    -- is exactly corrOf-eq (the correction of the reduction).
    h=ract : ∀ c b → let (b' , c') = hᶜ c b in
             secᶜ c • [ b ]ʷ ≈ₑ (fᶜ ʷ) b' • secᶜ c'
    h=ract c (inj₁ n)
      rewrite aux-fᶜ (conjss (rep c) [ n ]ʷ) = lemma-comm [ n ]ʷ (rep c)
    h=ract c (inj₂ x)
      rewrite aux-fᶜ (corrOf (_≈q_.sym (NQ.inv-nf∘nf=id {rep c • [ x ]ʷ}))) =
      corrOf-eq (_≈q_.sym (NQ.inv-nf∘nf=id {rep c • [ x ]ʷ}))

    open import Normalization.Reidemeister-Schreier

    -- Threading hᶜ through a right-embedded word advances the coset to the
    -- reduced representative (uniquely, since NFQ is canonical).
    lemma-adv : ∀ c a → (hᶜ ᵗ) c [ a ]ᵣ .proj₂ ≡ NQ.nf (rep c • a)
    lemma-adv c [ x ]ʷ = Eq.refl
    lemma-adv c ε = Eq.sym (Eq.trans (NQ.nf-cong _≈q_.right-unit) (nf∘inv c))
    lemma-adv c (a • a₁)
      rewrite lemma-adv c a
            | lemma-adv (NQ.nf (rep c • a)) a₁ =
      NQ.nf-cong (_≈q_.trans (_≈q_.cong NQ.inv-nf∘nf=id _≈q_.refl) _≈q_.assoc)

    -- ext is group-like.  An N-generator's inverse lifts from S; a
    -- quotient generator's inverse is its R̄-inverse corrected by the
    -- reduction word corrOf (proj₂ (PQ.gl x)) — the "corr-gl" data.
    private module PQ = _IsPresentationOf_ pQ

    grouplike : Grouplike ext
    grouplike (inj₁ n) = [ proj₁ (PN.gl n) ]ₗ , lefts (proj₂ (PN.gl n))
    grouplike (inj₂ x) =
      [ corrOf (proj₂ (PQ.gl x)) ⁻¹ₛ ]ₗ • [ proj₁ (PQ.gl x) ]ᵣ ,
      (_≈ₑ_.trans _≈ₑ_.assoc
        (_≈ₑ_.trans
          (_≈ₑ_.cong _≈ₑ_.refl
            (_≈ₑ_.trans (corrOf-eq (proj₂ (PQ.gl x))) _≈ₑ_.right-unit))
          (lefts inverseˡₛ)))

    -- Proposition 2.55.  Compatibility of conj / corr with G (soundness
    -- of the raw extension axioms) yields a presentation of G.
    --
    -- With `real : Realises`, the raw-axiom soundness needed by
    -- StarPresentation.GroupSem.GetSubPresentation is
    --     sound-t (sound-s real) sound-ax
    -- exactly as `sound-ax` is used in SemiDirectProduct.Presentation.
    -- What remains — following that file's subpres/dpres structure — is
    -- the coset normal form for the *twisted* relators: a group-likeness
    -- witness, a Reidemeister–Schreier NormalForm (nfp) and its
    -- UniqueNormalForm (unfp) giving `groupSubPres`, and surjectivity
    -- (`claim`), whence `dpres = isPresentationOf groupSubPres claim`.
    -- The two facts asked of the identity coset's representative.  A
    -- normal form with rep Iᶜ ≡ ε on the nose gives both by `rewrite`,
    -- which is how this used to be stated; asking for them separately is
    -- strictly weaker, and it has to be, because rep Iᶜ ≡ ε is
    -- unsatisfiable for a coset TOWER: one level of
    -- Normalization.CosetNF.SingleLevel.Transfer defines its inverse as
    -- gg (n , c) = (f ʷ) (g₁ n) • [ c ], a concatenation whatever its
    -- arguments, so above the base the two sides differ in head
    -- constructor.  (Examples.Groups.Symplectic.Simplified.NfEps proves
    -- this for the symplectic tower.)
    --
    -- Note that rep Iᶜ ≈q ε -- which every normal form gives for free,
    -- by inv-nf∘nf=id -- does NOT imply sec-triv: the right factor of
    -- ext carries EmptyRel, so a quotient equality reaches the extension
    -- only through corrOf-eq, picking up the correction [ corrOf p ]ₗ.
    -- sec-triv says exactly that that correction vanishes, i.e. that the
    -- representative is trivial in G and not merely in GQ.

    Sec-trivial : Set
    Sec-trivial = secᶜ Iᶜ ≈ₑ ε

    Conj-trivial : Set
    Conj-trivial = ∀ (x : N) → conjss (rep Iᶜ) [ x ]ʷ ≈s [ x ]ʷ

    -- The identity coset's representative reduces to ε using only
    -- axioms that lift exactly.  This is a statement purely about the
    -- QUOTIENT presentation: no extension, no corrections, no coset
    -- machinery — just a derivation in a restricted calculus.
    Sec-reduction : Set
    Sec-reduction = rep Iᶜ ≈₀ ε

    -- ... and it suffices.  This is what rights₀ buys: the quotient fact
    -- rep Iᶜ ≈q ε is free (inv-nf∘nf=id) but useless here, whereas the
    -- same reduction carried out in Corr-free lands in the extension
    -- with no Pauli left over.
    sec-trivial-from : Sec-reduction → Sec-trivial
    sec-trivial-from = rights₀

    -- ... but demanding every axiom be correction-free is stronger than
    -- necessary, and sometimes too strong.  The corrections are elements
    -- of N, so a derivation may use corrected axioms freely as long as
    -- what they accumulate CANCELS.  And whether it cancels need not be
    -- read off the derivation at all: corrOf-eq says
    --
    --     [ rep Iᶜ ]ᵣ  ≈ₑ  [ corrOf p ]ₗ • [ ε ]ᵣ,
    --
    -- so pushing that through the semantics pins incl ⟦ corrOf p ⟧N to
    -- the value of the representative in G.  If that value is the
    -- identity, then incl-injective and completeness of pN force
    -- corrOf p ≈s ε, whatever derivation p happened to be.
    --
    -- So Sec-trivial reduces to a SEMANTIC fact — the identity coset's
    -- representative denotes the identity of G — with no syntactic
    -- reduction to replay and no restriction on which axioms may be
    -- used.  Note this is strictly weaker than asking rep Iᶜ ≈q ε (which
    -- is free but says only that its QUOTIENT image is trivial): it says
    -- the lift is trivial too, which is exactly the content of
    -- Sec-trivial, now stated where it can be checked by evaluation.
    sec-trivial-semantic :
      (real : Realises) →
      (sound-ax : ∀ {w v} → extp w v → Gm._≈_ ⟦ w ⟧ ⟦ v ⟧) →
      Gm._≈_ ⟦ secᶜ Iᶜ ⟧ Gm.ε →
      Sec-trivial
    sec-trivial-semantic real sound-ax triv =
      _≈ₑ_.trans (corrOf-eq p)
        (_≈ₑ_.trans (_≈ₑ_.cong (lefts corr≈ε) _≈ₑ_.refl) _≈ₑ_.left-unit)
      where
      module EC = E.Cong (sound-t (sound-s real) sound-ax)

      p : rep Iᶜ ≈q ε
      p = NQ.inv-nf∘nf=id

      -- incl of the accumulated correction is the representative's value.
      incl-corr : Gm._≈_ (incl ⟦ corrOf p ⟧N) Gm.ε
      incl-corr =
        Gm.trans (Gm.sym (emb-l real (corrOf p)))
          (Gm.trans (Gm.sym (Gm.identityʳ ⟦ [ corrOf p ]ₗ ⟧))
            (Gm.trans (Gm.sym (EC.fʷ-cong (corrOf-eq p))) triv))

      -- so the correction is trivial in N, hence as a word.
      corr≈ε : corrOf p ≈s ε
      corr≈ε =
        πG.IsGroupMonomorphism.injective
          (πG.IsGroupIsomorphism.isGroupMonomorphism PN.iso)
          (GNm.trans (Extension.incl-injective et
                       (Gm.trans incl-corr (Gm.sym incl-ε)))
                     (GNm.sym PN-ε))

    dpres :
      Realises →
      (sound-ax : ∀ {w v} → extp w v → Group._≈_ G ⟦ w ⟧ ⟦ v ⟧) →
      (sec-triv : Sec-trivial) →
      (conj-triv : Conj-trivial) →
      -- The quotient realisation: each rep generator projects to its
      -- quotient value in GQ.
      (real-Q : ∀ x → GQm._≈_ (proj ⟦ inj₂ x ⟧₀) ⟦ [ x ]ʷ ⟧Q) →
      ext IsPresentationOf G
    dpres real sound-ax sec-triv conj-triv real-Q = isPresentationOf subpres claim
      where
      -- RS hypothesis (4): the identity coset's section is trivial.
      [I]≈ε : secᶜ Iᶜ ≈ₑ ε
      [I]≈ε = sec-triv

      -- The section law [c] • w ≈ [w']ₓ • [c'] from the RightAction engine
      -- (needs f-wd-ax/[I]≈ε/h=ract, NOT h-wd-ax — no circularity).
      module RAᶜ = Star-Injective-Full.RightAction
                     S ext Cᶜ Iᶜ fᶜ hᶜ f-wd-ax secᶜ [I]≈ε h=ract
      hᵗ-hyp : ∀ c w → let (w' , c') = (hᶜ ᵗ) c w in
               secᶜ c • w ≈ₑ (fᶜ ʷ) w' • secᶜ c'
      hᵗ-hyp = RAᶜ.lemma-⊛

      -- RS hypothesis (1): hᶜ inverts fᶜ on the identity coset.  The
      -- action of an N-generator there is conjugation by rep Iᶜ, so this
      -- is conj-triv read backwards; the coset is unchanged.
      h=⁻¹f-gen : ∀ (x : N) → CT._~_ ([ x ]ʷ , Iᶜ) ((hᶜ ᵗ) Iᶜ (fᶜ x))
      h=⁻¹f-gen x = _≈s_.sym (conj-triv x) , Eq.refl

      -- Full soundness (congruence, not just axioms) into G.
      module EC = E.Cong (sound-t (sound-s real) sound-ax)
      sound-full : ∀ {w v} → w ≈ₑ v → Gm._≈_ ⟦ w ⟧ ⟦ v ⟧
      sound-full = EC.fʷ-cong

      -- pN is injective on N-words.
      pN-inj : ∀ {w v} → GNm._≈_ ⟦ w ⟧N ⟦ v ⟧N → w ≈s v
      pN-inj = πG.IsGroupMonomorphism.injective
                 (πG.IsGroupIsomorphism.isGroupMonomorphism PN.iso)

      -- Faithfulness of the left embedding, via the semantics: [w]ₗ ≈ [v]ₗ
      -- lands, through G, in incl(⟦w⟧N) ≈ incl(⟦v⟧N), whence w ≈s v.
      faithful : ∀ {w v} → [ w ]ₗ ≈ₑ [ v ]ₗ → w ≈s v
      faithful {w} {v} e = pN-inj (Extension.incl-injective et
        (Gm.trans (Gm.sym (emb-l real w))
          (Gm.trans (sound-full e) (emb-l real v))))

      open Group-Lemmas ext grouplike using (•-cancelʳ)

      -- N-component well-definedness, uniformly: the section law turns an
      -- ext-axiom into  [w_u]ₗ • sec c_u ≈ [w_t]ₗ • sec c_t; equal cosets
      -- cancel the section, and faithfulness gives w_u ≈s w_t.
      n-wd : ∀ (c : Cᶜ) {u t} → ext u t →
             (hᶜ ᵗ) c u .proj₂ ≡ (hᶜ ᵗ) c t .proj₂ →
             (hᶜ ᵗ) c u .proj₁ ≈s (hᶜ ᵗ) c t .proj₁
      n-wd c {u} {t} ax ce = faithful faith
        where
        step : (fᶜ ʷ) ((hᶜ ᵗ) c u .proj₁) • secᶜ ((hᶜ ᵗ) c u .proj₂)
             ≈ₑ (fᶜ ʷ) ((hᶜ ᵗ) c t .proj₁) • secᶜ ((hᶜ ᵗ) c t .proj₂)
        step = _≈ₑ_.trans (_≈ₑ_.sym (hᵗ-hyp c u))
                 (_≈ₑ_.trans (_≈ₑ_.cong _≈ₑ_.refl (_≈ₑ_.axiom ax)) (hᵗ-hyp c t))
        step' : (fᶜ ʷ) ((hᶜ ᵗ) c u .proj₁) • secᶜ ((hᶜ ᵗ) c u .proj₂)
              ≈ₑ (fᶜ ʷ) ((hᶜ ᵗ) c t .proj₁) • secᶜ ((hᶜ ᵗ) c u .proj₂)
        step' = Eq.subst
          (λ □ → (fᶜ ʷ) ((hᶜ ᵗ) c u .proj₁) • secᶜ ((hᶜ ᵗ) c u .proj₂)
               ≈ₑ (fᶜ ʷ) ((hᶜ ᵗ) c t .proj₁) • secᶜ □)
          (Eq.sym ce) step
        faith : [ (hᶜ ᵗ) c u .proj₁ ]ₗ ≈ₑ [ (hᶜ ᵗ) c t .proj₁ ]ₗ
        faith = Eq.subst₂ _≈ₑ_ (aux-fᶜ ((hᶜ ᵗ) c u .proj₁))
                  (aux-fᶜ ((hᶜ ᵗ) c t .proj₁)) (•-cancelʳ step')

      -- Coset-component well-definedness, per axiom.
      coset-wd : ∀ (c : Cᶜ) {u t} → ext u t →
                 (hᶜ ᵗ) c u .proj₂ ≡ (hᶜ ᵗ) c t .proj₂
      coset-wd c (left {a} {b} x) =
        Eq.trans (Eq.cong proj₂ (lemma-hᶜ-left c a))
                 (Eq.sym (Eq.cong proj₂ (lemma-hᶜ-left c b)))
      coset-wd c (right ())
      coset-wd c (mid (left (comm n x')))
        rewrite lemma-hᶜ-left c (conj x' n) = Eq.refl
      coset-wd c (mid (right (tw {a} {b} r̄)))
        rewrite lemma-hᶜ-left c (corr r̄) =
        Eq.trans (lemma-adv c a)
          (Eq.trans (NQ.nf-cong (_≈q_.cong _≈q_.refl (_≈q_.axiom r̄)))
                    (Eq.sym (lemma-adv c b)))

      h-wd-ax : ∀ (c : Cᶜ) {u t} → ext u t →
                CT._~_ ((hᶜ ᵗ) c u) ((hᶜ ᵗ) c t)
      h-wd-ax c ax = n-wd c ax (coset-wd c ax) , coset-wd c ax

      -- The coset normal form for ext, transported from the N-factor's
      -- normal form: NF_ext = NFS × NFQ.  (The Reidemeister–Schreier engine
      -- packaged in CT.Transfer, now that all five hypotheses hold.)
      module CTT = CT.Transfer h=⁻¹f-gen h-wd-ax f-wd-ax [I]≈ε h=ract
      nfp = CTT.nfp' NS.normalForm

      ----------------------------------------------------------------
      -- Assembly: nfp + soundness + surjectivity  ⇒  presentation.

      -- A right-embedded word projects to its quotient value.
      emb-r-Q : ∀ w → GQm._≈_ (proj ⟦ [ w ]ᵣ ⟧) ⟦ w ⟧Q
      emb-r-Q [ x ]ʷ = real-Q x
      emb-r-Q ε = GQm.trans proj-ε (GQm.sym PQ-ε)
      emb-r-Q (w • v) =
        GQm.trans (proj-∙ ⟦ [ w ]ᵣ ⟧ ⟦ [ v ]ᵣ ⟧)
          (GQm.trans (GQm.∙-cong (emb-r-Q w) (emb-r-Q v)) (GQm.sym (PQ-∙ w v)))

      -- (fᶜ ʷ) w reads as incl of its N-value.
      emb-fᶜ : ∀ w → Gm._≈_ ⟦ (fᶜ ʷ) w ⟧ (incl ⟦ w ⟧N)
      emb-fᶜ w = Eq.subst (λ □ → Gm._≈_ ⟦ □ ⟧ (incl ⟦ w ⟧N))
                          (Eq.sym (aux-fᶜ w)) (emb-l real w)

      module NFP = SNF.NormalForm nfp

      -- The inverse normal form gg(a,c) reads as incl(N-part) • coset.
      sem-gg : ∀ a c → Gm._≈_ ⟦ NFP.inv-nf (a , c) ⟧
                             (incl ⟦ NS.inv-nf a ⟧N Gm.∙ ⟦ [ rep c ]ᵣ ⟧)
      sem-gg a c = Gm.∙-cong (emb-fᶜ (NS.inv-nf a)) Gm.refl

      -- Right cancellation in G.
      G-cancelʳ : ∀ {a b x} → Gm._≈_ (a Gm.∙ x) (b Gm.∙ x) → Gm._≈_ a b
      G-cancelʳ {a} {b} {x} eq = Gm.trans (Gm.sym (Gm.identityʳ a))
        (Gm.trans (Gm.∙-cong Gm.refl (Gm.sym (Gm.inverseʳ x)))
          (Gm.trans (Gm.sym (Gm.assoc a x (x Gm.⁻¹)))
            (Gm.trans (Gm.∙-cong eq Gm.refl)
              (Gm.trans (Gm.assoc b x (x Gm.⁻¹))
                (Gm.trans (Gm.∙-cong Gm.refl (Gm.inverseʳ x)) (Gm.identityʳ b))))))

      -- Projecting gg(a,c) recovers the coset's quotient value.
      proj-cong = πp.IsGroupHomomorphism.⟦⟧-cong (Extension.proj-homo et)
      proj-sem : ∀ a c → GQm._≈_ (proj ⟦ NFP.inv-nf (a , c) ⟧) ⟦ rep c ⟧Q
      proj-sem a c = GQm.trans (proj-cong (sem-gg a c))
        (GQm.trans (proj-∙ (incl ⟦ NS.inv-nf a ⟧N) ⟦ [ rep c ]ᵣ ⟧)
          (GQm.trans (GQm.∙-cong (Extension.proj-kills-incl et ⟦ NS.inv-nf a ⟧N) GQm.refl)
            (GQm.trans (GQm.identityˡ (proj ⟦ [ rep c ]ᵣ ⟧)) (emb-r-Q (rep c)))))

      -- Unique normal form: equal denotations force equal NF pairs.
      unfp : NFU.UniqueNormalForm ext (Eq.setoid (NFS × NFQ))
               (Group.setoid G) ⟦_⟧ (SNF.NormalForm.inv-nf nfp)
      unfp = record { unique = uniq }
        where
        uniq : ∀ {u v : NFS × NFQ} →
               Gm._≈_ ⟦ NFP.inv-nf u ⟧ ⟦ NFP.inv-nf v ⟧ → u ≡ v
        uniq {a , c} {a' , c'} eq = Eq.cong₂ _,_ a≡a' c≡c'
          where
          c≡c' : c ≡ c'
          c≡c' = Eq.trans (Eq.sym (nf∘inv c))
            (Eq.trans (NQ.nf-cong (PQ-inj
              (GQm.trans (GQm.sym (proj-sem a c))
                (GQm.trans (proj-cong eq) (proj-sem a' c')))))
              (nf∘inv c'))
          gg-eq : Gm._≈_ (incl ⟦ NS.inv-nf a ⟧N Gm.∙ ⟦ [ rep c ]ᵣ ⟧)
                         (incl ⟦ NS.inv-nf a' ⟧N Gm.∙ ⟦ [ rep c ]ᵣ ⟧)
          gg-eq = Eq.subst
            (λ □ → Gm._≈_ (incl ⟦ NS.inv-nf a ⟧N Gm.∙ ⟦ [ rep c ]ᵣ ⟧)
                          (incl ⟦ NS.inv-nf a' ⟧N Gm.∙ ⟦ [ rep □ ]ᵣ ⟧))
            (Eq.sym c≡c')
            (Gm.trans (Gm.sym (sem-gg a c)) (Gm.trans eq (sem-gg a' c')))
          a≡a' : a ≡ a'
          a≡a' = Eq.trans (Eq.sym (nf∘invS a))
            (Eq.trans (NS.nf-cong
              (pN-inj (Extension.incl-injective et (G-cancelʳ gg-eq))))
              (nf∘invS a'))

      module SP = Normalization.StarPresentation ext (Eq.setoid (NFS × NFQ))
      module GS = SP.GroupSem G ⟦_⟧₀
      subpres : ext IsSubPresentationOf G
      subpres = GS.GetSubPresentation.groupSubPres
                  (sound-t (sound-s real) sound-ax) grouplike nfp unfp

      -- Surjectivity: pick a rep word xw with ⟦xw⟧Q = proj g; then
      -- g · ⟦[xw]ᵣ⟧⁻¹ ∈ ker(proj) = im(incl) is incl n = ⟦[nw]ₗ⟧, so
      -- g = ⟦[nw]ₗ • [xw]ᵣ⟧.
      claim : Surjective _≈ₑ_ Gm._≈_ ⟦_⟧
      claim g = [ nw ]ₗ • [ xw ]ᵣ , λ z≈ → Gm.trans (sound-full z≈) g-eq
        where
        xw : Word X
        xw = proj₁ (PQ-surj (proj g))
        ⟦xw⟧≈ : GQm._≈_ ⟦ xw ⟧Q (proj g)
        ⟦xw⟧≈ = proj₂ (PQ-surj (proj g)) _≈q_.refl
        ker-elt : Gm.Carrier
        ker-elt = g Gm.∙ (Gm._⁻¹ ⟦ [ xw ]ᵣ ⟧)
        ker-proj : GQm._≈_ (proj ker-elt) GQm.ε
        ker-proj = GQm.trans (proj-∙ g (Gm._⁻¹ ⟦ [ xw ]ᵣ ⟧))
          (GQm.trans (GQm.∙-cong GQm.refl
            (GQm.trans (πp.IsGroupHomomorphism.⁻¹-homo (Extension.proj-homo et) ⟦ [ xw ]ᵣ ⟧)
              (GQm.⁻¹-cong (GQm.trans (emb-r-Q xw) ⟦xw⟧≈))))
            (GQm.inverseʳ (proj g)))
        n : GNm.Carrier
        n = proj₁ (Extension.ker⊆im-incl et ker-elt ker-proj)
        incl-n≈ : Gm._≈_ (incl n) ker-elt
        incl-n≈ = proj₂ (Extension.ker⊆im-incl et ker-elt ker-proj)
        nw : Word N
        nw = proj₁ (PN-surj n)
        ⟦nw⟧≈ : GNm._≈_ ⟦ nw ⟧N n
        ⟦nw⟧≈ = proj₂ (PN-surj n) _≈s_.refl
        g-eq : Gm._≈_ ⟦ [ nw ]ₗ • [ xw ]ᵣ ⟧ g
        g-eq = Gm.trans (Gm.∙-cong (emb-l real nw) Gm.refl)
          (Gm.trans (Gm.∙-cong (incl-cong ⟦nw⟧≈) Gm.refl)
            (Gm.trans (Gm.∙-cong incl-n≈ Gm.refl)
              (Gm.trans (Gm.assoc g (Gm._⁻¹ ⟦ [ xw ]ᵣ ⟧) ⟦ [ xw ]ᵣ ⟧)
                (Gm.trans (Gm.∙-cong Gm.refl (Gm.inverseˡ ⟦ [ xw ]ᵣ ⟧))
                          (Gm.identityʳ g)))))
