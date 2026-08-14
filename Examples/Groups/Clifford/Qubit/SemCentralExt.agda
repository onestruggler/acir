------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the qubit Clifford group as a CENTRAL extension:
--
--     1 ─→ ℤ/8 ─→ ℤ/8 ×_c Q ─→ Q ─→ 1,
--
-- from ForStdlib.Algebra.Construct.CentralExtension, with K = ⟨ω⟩ ≅ ℤ/8
-- and Q the group presented by Figure8-Mod-Scalar.  This is the same
-- extension Qubit.SemFE builds as a twisted product ℤ/8 ×_f Q, said in
-- the vocabulary that fits it: the scalars are central, so there is no
-- action to carry and a factor set is just a 2-cocycle.
--
-- Nothing is reproved here.  A Cocycle's four fields are exactly a
-- FactorSet's for the TRIVIAL action — `act x u` reduces to `u`, so even
-- the cocycle identity has the same type on the nose — and SemFE's φ IS
-- that trivial action.  So γᶜ below is SemFE.γ, projected; and what this
-- file adds is the part the twisted-product vocabulary cannot state:
--
--   * incl-central — the image of the kernel really is central in the
--     total group.  ForStdlib's CentralExtension says so in its header
--     and builds the group accordingly, but never proves it; the proof
--     is two normalisations (c ε y = ε = c y ε) and commutativity of the
--     kernel, and it belongs upstream rather than here;
--
--   * same-∙ and same-⁻¹ — the central extension and the twisted product
--     over the same cocycle carry the very same multiplication and the
--     same inverse, by `refl`.  This is the claim FactorSetExtension's
--     header makes ("a trivial action gives exactly the multiplication of
--     the central extension"), checked rather than asserted.  The inverse
--     is where the two look different on paper: the twisted product's is
--     act (x⁻¹) ((a · f x x⁻¹)⁻¹), and the action is what disappears.
--
-- All three are stated for an ARBITRARY cocycle over arbitrary A and H,
-- and hold of γᶜ by instantiation.  That is not fastidiousness about
-- generality: stated at γᶜ they do not typecheck.  The terms being
-- compared contain c applied to arguments, conversion stops being
-- syntactic, and Agda normalises the cocycle — which at this instance
-- means unfolding the section, the bijective normal form and the whole
-- of ScalarKernel, at a cost of tens of gigabytes.  With the cocycle a
-- variable, nothing can unfold and each proof is a few lines.  γᶜ-is-γ
-- is the bridge back, and it is safe because it compares the two by one
-- projection rather than through their values.
--
-- Why the extension is central is, at bottom, a fact about Figure 8 and
-- not about this construction: ω commutes with every circuit (comm₀ of
-- the circuit framework, via Figure8.ω^-central).  That is SemFE's
-- scalar-central, re-exported below, and it is what makes ℤ/8 ×_c Q the
-- right model of the scalar layer rather than merely a group.
--
-- The contrast that gives the file its point: with c ≡ 0 the same
-- construction returns the DIRECT product ℤ/8 × Q (Direct-group), the
-- split extension in which a word's scalar can be read off the word.
-- Figure 8 is not of that form, so γᶜ is not a coboundary.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.SemCentralExt where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Level using (Level ; 0ℓ ; _⊔_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
import ForStdlib.Algebra.Construct.CentralExtension as CE
open CE using (Cocycle)
import ForStdlib.Algebra.Construct.FactorSetExtension as FSE
open FSE using (FactorSet)

-- K, Q and the trivial action are SemFE's, not copies: the whole point
-- is that this is the same extension.  γ is its factor set, `section`
-- having discharged the only hypothesis it had.
open import Examples.Groups.Clifford.Qubit.SemFE
  using (K ; Q ; φ ; γ)

-- Centrality of the scalar, re-exported: ω commutes with every Figure-8
-- circuit.  This is what says the extension below is the scalar layer,
-- and it is why there is no action in sight — the quotient would act on
-- ⟨ω⟩ by conjugation, and ω is central.
open import Examples.Groups.Clifford.Qubit.SemFE
  using (scalar-central) public

------------------------------------------------------------------------
-- γᶜ: the 2-cocycle
--
-- SemFE's factor set, read as a cocycle.  Every field transfers with no
-- adjustment because the action is trivial: IsNormalisedCocycle's
-- cocycle identity is
--
--     f x y ∙ f (x·y) z ≈ act x (f y z) ∙ f x (y·z)
--
-- and `act x` is the identity by definition, which is Cocycle's identity
-- verbatim.
--
-- Concretely, c x y is the exponent of the scalar by which the chosen
-- lifts of x and y fail to multiply: pick the representative word of
-- each class, read both in Figure 8's alphabet, and compare their
-- product with the representative of the product.  It exists because the
-- kernel of the quotient is the scalars (Selinger.ScalarKernel.kernel)
-- and it is well defined because ω has order exactly 8
-- (Model.Faithful.ω-faithful).

γᶜ : (n : ℕ) → Cocycle K (Q n)
γᶜ n = record
  { c       = FS.f
  ; c-cong  = FS.f-cong
  ; c-εˡ    = FS.f-εˡ
  ; c-εʳ    = FS.f-εʳ
  ; cocycle = FS.cocycle
  }
  where module FS = FactorSet (γ n)

------------------------------------------------------------------------
-- The central extension

-- The total group: pairs (scalar , circuit mod scalars), multiplied with
-- the cocycle correction.
Central-group : (n : ℕ) → Group 0ℓ 0ℓ
Central-group n = CE.group K (Q n) (γᶜ n)

Central-extension : (n : ℕ) → Extension (AbelianGroup.group K) (Q n)
Central-extension n = CE.centralExtension K (Q n) (γᶜ n)

------------------------------------------------------------------------
-- What the construction gives, for any cocycle
--
-- Centrality of the kernel, and agreement with the twisted product.
-- Generic for the reason given in the header: at γᶜ these do not
-- typecheck, because comparing terms that mention c forces the cocycle
-- to be normalised.  Each holds of γᶜ by instantiating A, H and γ'.

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
-- The bridge back to SemFE
--
-- The cocycle of the central extension IS the factor set of the twisted
-- product — one projection of a record literal on each side, so this
-- never has to look at what either function computes.

γᶜ-is-γ : (n : ℕ) → Cocycle.c (γᶜ n) ≡ FactorSet.f (γ n)
γᶜ-is-γ n = Eq.refl

-- The three generic results at the scalar layer.  Applying a generic
-- lemma at γᶜ costs nothing — an application never has to look inside
-- the cocycle — so these are the concrete statements, obtained the only
-- way they can be.  Their types are left to be inferred: writing one out
-- would name c at arguments, which is the thing that does not check.

incl-central-ms = λ (n : ℕ) → incl-central K (Q n) (γᶜ n)

same-∙-ms       = λ (n : ℕ) → same-∙ K (Q n) (γᶜ n)

same-⁻¹-ms      = λ (n : ℕ) → same-⁻¹ K (Q n) (γᶜ n)

------------------------------------------------------------------------
-- The split instance
--
-- c ≡ 0 is a cocycle, and the extension it names is the DIRECT product
-- ℤ/8 × Q: the one in which the scalar of a product is the sum of the
-- scalars, i.e. in which w ↦ (0 , w) is a homomorphic section.  Figure 8
-- is not of that form — that is what γᶜ being cohomologically nontrivial
-- means, and it is why ω-faithfulness had to come from a model.

γᶜ-split : (n : ℕ) → Cocycle K (Q n)
γᶜ-split n = CE.trivialCocycle K (Q n)

Direct-group : (n : ℕ) → Group 0ℓ 0ℓ
Direct-group n = CE.group K (Q n) (γᶜ-split n)

Direct-extension : (n : ℕ) → Extension (AbelianGroup.group K) (Q n)
Direct-extension n = CE.centralExtension K (Q n) (γᶜ-split n)
