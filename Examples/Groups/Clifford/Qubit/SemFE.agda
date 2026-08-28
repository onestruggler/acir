------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the qubit Clifford group as a twisted product:
--
--     1 ─→ ℤ/8 ─→ ℤ/8 ×_f Q ─→ Q ─→ 1,
--
-- the factor-set presentation, from
-- ForStdlib.Algebra.Construct.FactorSetExtension (Rotman, Theorem 9.8),
-- of the extension that Qubit.ExactExtension builds concretely:
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ (Figure 8 mod scalars) ─→ 1.
--
-- The quotient is taken SYNTACTICALLY here — Q is the group presented by
-- Figure8-Mod-Scalar, words over the symplectic alphabet modulo ≈ᵐˢ —
-- rather than in the structural model VSp n that ExactExtension projects
-- onto.  That is the whole reason this layer is cheap: the defect of a
-- lifting is then measured by Selinger.ScalarKernel.kernel, which is an
-- induction on mod-scalar derivations and needs neither the P4 action
-- nor completeness.
--
-- Theorem 9.8 asks for four ingredients:
--
--   * K = the scalars ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of
--     ω, as an AbelianGroup bundle (+-0-abelianGroup 6);
--   * Q = the group of the mod-scalar rule set, which is a group because
--     that rule set is grouplike (Selinger.GroupLike.grouplike-MS);
--   * φ = the action of Q on K, which is TRIVIAL: ω is central in
--     Figure 8, so the extension is central.  Unlike the Pauli layer
--     (Qubit.Semantics.Sem3, where φ is the linear action of a symplectic map)
--     there is nothing to compute — but it is a fact about Figure 8, not
--     a convention, so scalar-central below states it;
--   * γ = a factor set for φ.
--
-- φ and γ are both built here in full, with no hypotheses left.
--
-- γ is the factor set of a LIFTING, and a lifting needs a section of the
-- quotient: a choice rep of one word per mod-scalar class, taking ε to ε
-- (the record `Section`).  That record is the construction's only input,
-- and it is discharged at the end of the file from
--
--   * ProjectiveClifford.Qubit.Selinger.Presentation.bijective-ms, the
--     bijective normal form of exactly this rule set, together with
--   * Normalization.NormalForm.Setoid.ε-section, which moves a
--     Bijection's section to ε at the identity class.  A section is not
--     part of a Bijection's data — inv-nf y is proj₁ (surjective y) — so
--     it can be changed at one index without touching the map, its
--     congruence or its injectivity; NF-ms-dec is what it takes to see
--     that index, and the decision never has to reduce.
--
-- Given the section, everything else is proved:
--
--   ℓ = E ∘ rep   is a lifting of Q into Figure 8 (E is Selinger.Relabel's
--                 relabelling, which is where the two alphabets differ),
--   f w v         is the exponent of the scalar by which ℓ w · ℓ v and
--                 ℓ (w · v) differ — it EXISTS by ScalarKernel.kernel,
--                 which is exactly the statement that the kernel of the
--                 quotient is the scalars, and
--   f-cong, f-εˡ, f-εʳ and the cocycle identity all follow from that
--                 defect being UNIQUE, which is ω-faithfulness
--                 (Model.Faithful.ω-faithful — a theorem at every width,
--                 by the mod-17 matrix model) together with cancellation
--                 in the grouplike Figure-8 presentation.
--
-- Nothing in the construction depends on how the section is obtained, so
-- the two halves stay separate: the factor set is developed against the
-- record, and discharged once at the end.
--
-- What the trivial factor set gives here, by contrast, is the DIRECT
-- product ℤ/8 × Q (the action being trivial as well): the split
-- extension, in which the scalar can be read off a word.  That is not
-- the Clifford group — Figure 8 is not split over its scalars — which is
-- what makes γ worth building.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.SemFE where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Fin using (toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat as Nat using (ℕ ; _%_ ; _/_)
open import Data.Nat.DivMod using (m%n<n ; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (*-comm)
open import Data.Product using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; ε ; _•_ ; _^_)

import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Normalization.NormalForm.Setoid as SNF

open import ForStdlib.Data.Fin.Mod using (ℤ ; +-0-abelianGroup)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action)
import ForStdlib.Algebra.Construct.FactorSetExtension as FSE
open FSE using (FactorSet)

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; Circuit)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8 using (ω ; _≈ᶠ_ ; ω^-central)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar
  p-2 p-prime as MS

-- The mod-scalar rule set is grouplike: C2, C3 and C5 give each gate a
-- left inverse, cong↑ shifts one up a wire.
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.GroupLike
  using (grouplike-MS)

-- The bijective normal form of that same rule set, and decidability of
-- its values: between them they discharge the section, at the end.
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Presentation
  using (bijective-ms ; NF-ms-dec)
open import Examples.Groups.Symplectic.Normalization.Boxes p-2 p-prime
  using (NF)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli)

-- The kernel of the quotient: two words equal mod scalars have E-images
-- equal in Figure 8 up to a power of ω.  This is what makes the defect
-- of a lifting a scalar, i.e. what makes f exist.
import Examples.Groups.Clifford.Qubit.Selinger.ScalarKernel p-2 p-prime as SK
open SK using (_≈ᵐˢ_)

-- The two sides live over different alphabets — Figure 8 over ExactGate,
-- the quotient over SympGate — and E is the translation.
open import Examples.Groups.Clifford.Qubit.Selinger.Relabel p-2 p-prime
  using (E)

-- The scalar k ↦ ωᵏ, and its faithfulness: ω has order exactly 8.
import Examples.Groups.Clifford.Qubit.ExactExtension as EE
open EE using (scalar)
open import Examples.Groups.Clifford.Qubit.Model.Faithful using (ω-faithful)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- K: the scalars ⟨ω⟩ ≅ ℤ/8
--
-- Written additively in the exponent of ω, as in Qubit.ExactExtension —
-- whose Scalar-group is the Group bundle of this AbelianGroup.  (The
-- carrier check pins the order: +-0-abelianGroup m has carrier ℤ (₂₊ m),
-- so order 8 is m = 6, and an off-by-one here would silently change ω's
-- order.)

K : AbelianGroup 0ℓ 0ℓ
K = +-0-abelianGroup 6

private
  scalar-order-8 : AbelianGroup.Carrier K ≡ ℤ 8
  scalar-order-8 = Eq.refl

module K = AbelianGroup K

------------------------------------------------------------------------
-- Q: the group of Figure 8 mod scalars
--
-- The carrier is symplectic circuits and the equality is ≈ᵐˢ; it is a
-- group because the mod-scalar rule set is grouplike.

Q : (n : ℕ) → Group 0ℓ 0ℓ
Q n = Group-Lemmas.•-ε-group (n MS.CRel,_===_) (grouplike-MS {n})

private
  -- Q's equality is the mod-scalar congruence, on the nose.
  Q-≈ : {w v : Circuit n} → (w ≈ᵐˢ v) ≡ (Group._≈_ (Q n) w v)
  Q-≈ = Eq.refl

------------------------------------------------------------------------
-- φ: the action of Q on the scalars
--
-- Trivial, because ω is central in Figure 8 — the extension is a CENTRAL
-- extension, and a factor set for the trivial action is a 2-cocycle in
-- the ordinary sense.  Centrality is Figure8.ω^-central, an axiom of the
-- circuit framework (comm₀) rather than of Selinger's rule set; stating
-- it here is what makes the choice of φ a fact instead of a convention.

scalar-central : (k : ℤ 8) (w : F8.Circuit n) →
                 (scalar k • w) ≈ᶠ (w • scalar k)
scalar-central k w = ω^-central (toℕ k) w

φ : (n : ℕ) → Action (AbelianGroup.rawMonoid K) (Group.rawMonoid (Q n))
φ n = FSE.trivialAction K (Q n)

------------------------------------------------------------------------
-- The twisted product ℤ/8 ×_f Q
--
-- For any factor set γ = (f , laws) this is the group on ℤ/8 × Circuit n
-- with
--
--     (a , w) ∙ (b , v) = ((a + b) + f w v , w · v),
--
-- an extension of Q by ℤ/8 realising φ — so, the action being trivial, a
-- central extension.

Twisted : (n : ℕ) → FactorSet K (Q n) (φ n) → Group 0ℓ 0ℓ
Twisted n γ = FSE.group K (Q n) (φ n) γ

Twisted-extension : (n : ℕ) (γ : FactorSet K (Q n) (φ n)) →
                    Extension (AbelianGroup.group K) (Q n)
Twisted-extension n γ = FSE.factorSetExtension K (Q n) (φ n) γ

-- Theorem 9.8's necessity direction, in the form a client wants it: any
-- extension realising φ with a unit-preserving lifting determines its
-- factor set.
γ-of-lifting : {f : Circuit n → Circuit n → ℤ 8} →
               FSE.IsFactorSet K (Q n) (φ n) f → FactorSet K (Q n) (φ n)
γ-of-lifting {n} {f} ifs = record
  { f                   = f
  ; isNormalisedCocycle = FSE.isFactorSet⇒isNormalisedCocycle K (Q n) (φ n) ifs
  }

------------------------------------------------------------------------
-- Powers of the scalar
--
-- ExactExtension proves these too, but privately; ScalarKernel's Ω-+ and
-- Ω-8 are public, so they are re-derived here rather than exported from
-- there.  Ω n k is ω ^ k on the nose, which is why the two mix freely.

private

  mod8 : ℕ → ℤ 8
  mod8 m = fromℕ< (m%n<n m 8)

  -- Every multiple of 8 collapses (C1), so the exponent only matters
  -- modulo 8.
  pow-mult8 : (m : ℕ) → (ω {n} ^ ((m / 8) Nat.* 8)) ≈ᶠ ε
  pow-mult8 {n} m =
    PB.trans (PB.refl' _ (Eq.cong (ω ^_) (*-comm (m / 8) 8)))
             (SK.Ω-8 n (m / 8))

  pow-mod : (m : ℕ) → (ω {n} ^ (m % 8)) ≈ᶠ (ω ^ m)
  pow-mod {n} m =
    PB.sym (PB.trans (PB.refl' _ (Eq.cong (ω ^_) (m≡m%n+[m/n]*n m 8)))
             (PB.trans (SK.Ω-+ n (m % 8) ((m / 8) Nat.* 8))
               (PB.trans (PB.cong PB.refl (pow-mult8 m)) PB.right-unit)))

  -- ωᵐ is the scalar named by m mod 8.
  pow-scalar : (m : ℕ) → (ω {n} ^ m) ≈ᶠ scalar (mod8 m)
  pow-scalar m =
    PB.trans (PB.sym (pow-mod m))
             (PB.sym (PB.refl' _ (Eq.cong (ω ^_) (toℕ-fromℕ< (m%n<n m 8)))))

  -- ℤ/8 addition is ℕ addition modulo 8, on the nose.
  toℕ-∙ : (j k : ℤ 8) → toℕ (j K.∙ k) ≡ (toℕ j Nat.+ toℕ k) % 8
  toℕ-∙ j k = toℕ-fromℕ< (m%n<n (toℕ j Nat.+ toℕ k) 8)

  -- k ↦ ωᵏ turns ℤ/8 addition into concatenation.
  scalar-∙ : (j k : ℤ 8) → scalar {n} (j K.∙ k) ≈ᶠ (scalar j • scalar k)
  scalar-∙ {n} j k =
    PB.trans (PB.refl' _ (Eq.cong (ω ^_) (toℕ-∙ j k)))
             (PB.trans (pow-mod (toℕ j Nat.+ toℕ k))
                       (SK.Ω-+ n (toℕ j) (toℕ k)))

------------------------------------------------------------------------
-- Uniqueness of the scalar defect
--
-- Figure 8 is grouplike, so it cancels; and ω has order exactly 8
-- (Model.Faithful.ω-faithful, by the mod-17 matrix model).  Together:
-- the scalar separating two words is unique.  This is what turns the
-- EXISTENCE statement `defect` below into a FUNCTION's worth of data,
-- and it is what every cocycle law is proved by.

private
  module GL (m : ℕ) = Group-Lemmas (m F8.CRel,_===_) (F8.grouplike {m})

scalar-unique : {t u : F8.Circuit n} {j k : ℤ 8} →
                u ≈ᶠ (scalar j • t) → u ≈ᶠ (scalar k • t) → j ≡ k
scalar-unique {n} e₁ e₂ =
  ω-faithful (GL.•-cancelʳ n (PB.trans (PB.sym e₁) e₂))

------------------------------------------------------------------------
-- The hole: a normalised section of the quotient
--
-- A choice of one word per mod-scalar class, taking ε to ε.  rep-cong is
-- what makes ℓ = E ∘ rep well defined on Q — E itself is NOT, since it
-- sends a mod-scalar derivation to a Figure-8 one only up to a scalar,
-- which is precisely the defect f measures.
--
-- It is an input to the factor set below and a theorem at the end of the
-- file (`section`), so that the two halves do not have to be read
-- together: rep = inv-nf ∘ nf for the bijective normal form of this rule
-- set, with its section moved to ε at the identity class.

record Section (n : ℕ) : Set where
  field
    -- The chosen representative of a class.
    rep      : Circuit n → Circuit n
    -- It is in the class it represents.
    rep-≈    : (w : Circuit n) → rep w ≈ᵐˢ w
    -- It depends only on the class.
    rep-cong : {w v : Circuit n} → w ≈ᵐˢ v → rep w ≡ rep v
    -- Normalisation: the unit represents itself.
    rep-ε    : rep ε ≡ ε

------------------------------------------------------------------------
-- γ: the factor set of a section

module _ {n : ℕ} (σ : Section n) where

  open Section σ

  ----------------------------------------------------------------------
  -- The lifting

  -- Choose a representative, then read it in Figure 8's alphabet.
  ℓ : Circuit n → F8.Circuit n
  ℓ w = E (rep w)

  -- ℓ is a section of the quotient by construction, and it preserves the
  -- unit because the section is normalised (E ε is ε on the nose, E
  -- being a wmap).
  ℓ-ε : ℓ ε ≡ ε
  ℓ-ε = Eq.cong E rep-ε

  ℓ-cong : {w v : Circuit n} → w ≈ᵐˢ v → ℓ w ≡ ℓ v
  ℓ-cong e = Eq.cong E (rep-cong e)

  ----------------------------------------------------------------------
  -- The defect exists
  --
  -- rep (w · v) and rep w · rep v represent the same class, so their
  -- E-images differ by a scalar (ScalarKernel.kernel).  Note that
  -- E (rep w · rep v) IS ℓ w · ℓ v: E is a wmap, so it distributes over
  -- concatenation definitionally.  Moving the scalar to the front — where
  -- `factors` wants it — costs an inverse (7k, since ω⁻¹ = ω⁷) and one
  -- use of centrality.

  private
    rep-• : (w v : Circuit n) → rep (w • v) ≈ᵐˢ (rep w • rep v)
    rep-• w v =
      PB.trans (rep-≈ (w • v)) (PB.sym (PB.cong (rep-≈ w) (rep-≈ v)))

  defect : (w v : Circuit n) →
           ∃ λ k → (ℓ w • ℓ v) ≈ᶠ ((ω ^ k) • ℓ (w • v))
  defect w v with SK.kernel (rep-• w v)
  ... | k , e = 7 Nat.* k ,
    PB.trans (PB.sym PB.right-unit)
      (PB.trans (PB.cong PB.refl (PB.sym (SK.Ω-inv n k)))
        (PB.trans (PB.sym PB.assoc)
          (PB.trans (PB.cong (PB.sym e) PB.refl)
                    (PB.sym (SK.Ω-central n (7 Nat.* k) (ℓ (w • v)))))))

  ----------------------------------------------------------------------
  -- The factor set

  -- f w v is the exponent of that scalar, read in ℤ/8.
  f : Circuit n → Circuit n → ℤ 8
  f w v = mod8 (proj₁ (defect w v))

  -- ... and it is the defect of ℓ: this is Theorem 9.8's `factors`.
  factors : (w v : Circuit n) →
            (ℓ w • ℓ v) ≈ᶠ (scalar (f w v) • ℓ (w • v))
  factors w v =
    PB.trans (proj₂ (defect w v))
             (PB.cong (pow-scalar (proj₁ (defect w v))) PB.refl)

  ----------------------------------------------------------------------
  -- The cocycle laws
  --
  -- Each is `factors` compared against a second, hand-built witness of
  -- the same shape, with scalar-unique to conclude.  Nothing here is
  -- specific to Clifford circuits: it is the usual argument that the
  -- defect of a lifting is a normalised 2-cocycle, done concretely
  -- because the extension itself is not available at this layer (its
  -- projection would need soundness of Figure 8 for the mod-scalar rule
  -- set, which is a separate induction).

  private

    -- The section collapses ≈ᵐˢ to ≡, so congruent arguments give
    -- literally the same three words, and the two defects are the same.
    f-cong : {w w' v v' : Circuit n} →
             w ≈ᵐˢ w' → v ≈ᵐˢ v' → f w v ≡ f w' v'
    f-cong {w} {w'} {v} {v'} ew ev =
      scalar-unique (factors w v)
        (PB.trans (PB.refl' _ (Eq.cong₂ _•_ (ℓ-cong ew) (ℓ-cong ev)))
          (PB.trans (factors w' v')
            (PB.cong PB.refl
              (PB.refl' _ (Eq.sym (ℓ-cong (PB.cong ew ev)))))))

    -- ℓ ε is ε, so multiplying by it is free: the defect is 0.
    f-εˡ : (w : Circuit n) → f ε w ≡ K.ε
    f-εˡ w = scalar-unique (factors ε w)
      (PB.trans (PB.refl' _ (Eq.cong (_• ℓ w) ℓ-ε))
        (PB.cong PB.refl
                 (PB.refl' _ (Eq.sym (ℓ-cong (PB.left-unit))))))

    f-εʳ : (w : Circuit n) → f w ε ≡ K.ε
    f-εʳ w = scalar-unique (factors w ε)
      (PB.trans (PB.cong PB.refl (PB.refl' _ ℓ-ε))
        (PB.trans PB.right-unit
          (PB.trans (PB.sym PB.left-unit)
            (PB.cong PB.refl
              (PB.refl' _ (Eq.sym (ℓ-cong (PB.right-unit))))))))

    -- Associativity of ℓ x · ℓ y · ℓ z, bracketed both ways: the left
    -- bracketing accumulates f x y then f (x·y) z, the right one f y z
    -- then f x (y·z), and centrality is what lets the second scalar of
    -- the right bracketing travel out past ℓ x.
    cocycleˡ : (x y z : Circuit n) →
               ((ℓ x • ℓ y) • ℓ z)
                 ≈ᶠ (scalar (f x y K.∙ f (x • y) z) • ℓ ((x • y) • z))
    cocycleˡ x y z =
      PB.trans (PB.cong (factors x y) PB.refl)
        (PB.trans PB.assoc
          (PB.trans (PB.cong PB.refl (factors (x • y) z))
            (PB.trans (PB.sym PB.assoc)
              (PB.cong (PB.sym (scalar-∙ (f x y) (f (x • y) z))) PB.refl))))

    cocycleʳ : (x y z : Circuit n) →
               (ℓ x • (ℓ y • ℓ z))
                 ≈ᶠ (scalar (f y z K.∙ f x (y • z)) • ℓ (x • (y • z)))
    cocycleʳ x y z =
      PB.trans (PB.cong PB.refl (factors y z))
        (PB.trans (PB.sym PB.assoc)
          (PB.trans (PB.cong (PB.sym (scalar-central (f y z) (ℓ x))) PB.refl)
            (PB.trans PB.assoc
              (PB.trans (PB.cong PB.refl (factors x (y • z)))
                (PB.trans (PB.sym PB.assoc)
                  (PB.cong (PB.sym (scalar-∙ (f y z) (f x (y • z))))
                           PB.refl))))))

    cocycle : (x y z : Circuit n) →
              (f x y K.∙ f (x • y) z) ≡ (f y z K.∙ f x (y • z))
    cocycle x y z =
      scalar-unique (cocycleˡ x y z)
        (PB.trans PB.assoc
          (PB.trans (cocycleʳ x y z)
            (PB.cong PB.refl
                     (PB.refl' _
                       (Eq.sym (ℓ-cong (PB.assoc {w = x} {v = y} {u = z})))))))

  -- The factor set of the section.
  factor-set : FactorSet K (Q n) (φ n)
  factor-set = record
    { f                   = f
    ; isNormalisedCocycle = record
      { f-cong  = f-cong
      ; f-εˡ    = f-εˡ
      ; f-εʳ    = f-εʳ
      ; cocycle = cocycle
      }
    }

------------------------------------------------------------------------
-- Discharging the section
--
-- rep = inv-nf ∘ nf, for the bijective normal form of the mod-scalar
-- rule set (Selinger.Presentation.bijective-ms — obtained there by
-- transporting the extension presentation's normal form along the
-- translation g).  Two of the three fields come with the record: rep-≈
-- is inv-nf∘nf=id and rep-cong is nf-cong under inv-nf.
--
-- The third, rep ε ≡ ε, is what ε-section supplies.  A Bijection's
-- section is not part of its data, so it may be redefined at the single
-- index nf ε, where the empty word discharges the surjectivity
-- obligation by nf-cong alone; NF-ms-dec is the decidability that lets
-- that index be seen.  Note the decision never has to REDUCE — rep-ε
-- comes from the two arguments being equal, not from computing with
-- them — which is why this works at a variable width, where nf ε is
-- stuck.

private
  module SNFms (n : ℕ) =
    SNF (n MS.CRel,_===_) (Eq.setoid (Pauli n × NF n))

  -- The normal form, with ε put at the identity class.
  bnf : (n : ℕ) → SNFms.BijectiveNormalForm n
  bnf n = SNFms.ε-section n (bijective-ms n) (NF-ms-dec n)

section : (n : ℕ) → Section n
section n = record
  { rep      = λ w → B.inv-nf (B.nf w)
  ; rep-≈    = λ w → B.inv-nf∘nf=id
  ; rep-cong = λ e → Eq.cong B.inv-nf (B.nf-cong e)
  ; rep-ε    = SNFms.ε-section-rep n (bijective-ms n) (NF-ms-dec n)
  }
  where module B = SNFms.BijectiveNormalForm n (bnf n)

------------------------------------------------------------------------
-- The factor set, and the twisted product it names
--
-- No hypotheses: γ n is the factor set of the qubit Clifford group's
-- scalar layer, and ℤ/8 ×_γ Q is that layer presented as pairs
-- (scalar , circuit mod scalars).

γ : (n : ℕ) → FactorSet K (Q n) (φ n)
γ n = factor-set (section n)

Exact-twisted : (n : ℕ) → Group 0ℓ 0ℓ
Exact-twisted n = Twisted n (γ n)

Exact-twisted-extension : (n : ℕ) → Extension (AbelianGroup.group K) (Q n)
Exact-twisted-extension n = Twisted-extension n (γ n)

------------------------------------------------------------------------
-- The split instance
--
-- f ≡ 0 is a factor set for any action, and with the action trivial the
-- twisted product it names is the DIRECT product ℤ/8 × Q — the extension
-- in which w ↦ (0 , w) is a homomorphism, i.e. in which a word's scalar
-- can be read off the word.  Figure 8 is not of that form: that is the
-- content of γ above being nonzero, and of ω-faithfulness being a
-- theorem about a model rather than about the rule set.

γ-split : (n : ℕ) → FactorSet K (Q n) (φ n)
γ-split n = FSE.trivialFactorSet K (Q n) (φ n)

Split-group : (n : ℕ) → Group 0ℓ 0ℓ
Split-group n = Twisted n (γ-split n)

Split-extension : (n : ℕ) → Extension (AbelianGroup.group K) (Q n)
Split-extension n = Twisted-extension n (γ-split n)
