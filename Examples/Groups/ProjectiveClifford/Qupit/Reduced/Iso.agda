{-# OPTIONS --cubical-compatible --safe #-}
------------------------------------------------------------------------
-- Presentations of groups
--
-- The id-isomorphism  Reduced.Clifford-Relations ≅ Paper-V1.Clifford-Relations.
--
-- Both rule sets are relations over the same alphabet and the same
-- words — Reduced re-exports Paper-V1's — so the candidate isomorphism
-- is the identity on words, as in Paper-V1.Iso, and the whole content is
-- the pair of well-definedness proofs:
--
--   f-well-defined : every Reduced axiom holds in Paper-V1;
--   g-well-defined : every Paper-V1 axiom holds in Reduced.
--
-- Reduced is Paper-V1 less semi-MR, so f sends each axiom to the
-- Paper-V1 axiom of the same name, and g does the same for fourteen of
-- the fifteen.  The fifteenth, semi-MR, is a theorem of the reduced
-- relation: Paper-V1.Lemmas.SemiMR derives it from order-S, order-H,
-- M-power and comm-HHSHHS, and is instantiated below at Reduced's
-- relation, which does not have it.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (id)
open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
import Presentation.Base as PB
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open GroupMorphisms

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import Notations

module Examples.Groups.ProjectiveClifford.Qupit.Reduced.Iso
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The Paper-V1 side is opened unqualified, for the shared generator
-- layer, as in Paper-V1.Iso.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen
import Examples.Groups.ProjectiveClifford.Qupit.Reduced.Syntactics
  p-3 p-prime g* g-gen as Red
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Iso
  p-3 p-prime g* g-gen as PIso
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  p-3 p-prime g* g-gen as GL
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.SemiMR
  p-3 p-prime g* g-gen as SM

module PapR = Clifford-Relations
module RedR = Red.Clifford-Relations

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The lemma layer at the reduced relation
--
-- The generic layer takes the rules it uses as parameters; here each is
-- passed as the Reduced axiom it is.  semi-MR is not among them, so the
-- derived rule below is a theorem of the fourteen rules alone.

-- Group-likeness, directly: the derivation needs cancellation, so this
-- witness cannot be transported back along g-well-defined, as
-- Paper-V1.Iso transports its own.
red-grouplike : Grouplike (RedR._QRel,_===_ n)
red-grouplike =
  GL.Paper-GroupLike.grouplike RedR._QRel,_===_
    (PB.axiom RedR.order-S) (PB.axiom RedR.order-H)
    (λ k → PB.axiom (RedR.M-power k)) (PB.axiom RedR.comm-HHSHHS)
    (PB.axiom RedR.order-CZ) RedR.lemma-cong↑

-- semi-MR, at every width.
module Derived (n : ℕ) =
  SM.SemiMR n (RedR._QRel,_===_ (₁₊ n))
    (PB.axiom RedR.order-S) (PB.axiom RedR.order-H)
    (λ k → PB.axiom (RedR.M-power k)) (PB.axiom RedR.comm-HHSHHS)
    (red-grouplike {₁₊ n})

------------------------------------------------------------------------
-- The isomorphism

module Theorem where

  -- f : Reduced → Paper-V1.  Every axiom is Paper-V1's, word for word.
  -- The structural layer is shared outright (the same Lift-Relation over
  -- the same gates), so comm₁ / comm₂ / cong↑ map constructor to
  -- constructor.
  f-well-defined : ∀ {n} → let open PB (PapR._QRel,_===_ n) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> RedR._QRel,_===_ n w v -> id w ≈₂ id v
  f-well-defined RedR.order-S        = PB.axiom PapR.order-S
  f-well-defined RedR.order-H        = PB.axiom PapR.order-H
  f-well-defined (RedR.M-power k)    = PB.axiom (PapR.M-power k)
  f-well-defined RedR.comm-HHSHHS    = PB.axiom PapR.comm-HHSHHS
  f-well-defined RedR.order-CZ       = PB.axiom PapR.order-CZ
  f-well-defined RedR.order-Ex       = PB.axiom PapR.order-Ex
  f-well-defined RedR.comm-CZ-S↑     = PB.axiom PapR.comm-CZ-S↑
  f-well-defined RedR.semi-M↑CZ      = PB.axiom PapR.semi-M↑CZ
  f-well-defined RedR.semi-Ex-S↑     = PB.axiom PapR.semi-Ex-S↑
  f-well-defined RedR.semi-Ex-H↑     = PB.axiom PapR.semi-Ex-H↑
  f-well-defined RedR.blake-c12      = PB.axiom PapR.blake-c12
  f-well-defined RedR.yang-baxter    = PB.axiom PapR.yang-baxter
  f-well-defined RedR.cz-slide       = PB.axiom PapR.cz-slide
  f-well-defined RedR.semi-CX↑-CZ↓   = PB.axiom PapR.semi-CX↑-CZ↓
  f-well-defined (RedR.comm₁ gt w)   = PB.axiom (PapR.comm₁ gt w)
  f-well-defined (RedR.comm₂ gt w)   = PB.axiom (PapR.comm₂ gt w)
  f-well-defined (RedR.cong↑ eq)     = PapR.lemma-cong↑ _ _ (f-well-defined eq)

  -- g : Paper-V1 → Reduced.  The same, except at semi-MR, which Reduced
  -- does not have as an axiom and proves instead.
  g-well-defined : ∀ {n} → let open PB (RedR._QRel,_===_ n) renaming (_≈_ to _≈₁_) in
    ∀ {u t} -> PapR._QRel,_===_ n u t -> id u ≈₁ id t
  g-well-defined PapR.order-S        = PB.axiom RedR.order-S
  g-well-defined PapR.order-H        = PB.axiom RedR.order-H
  g-well-defined (PapR.M-power k)    = PB.axiom (RedR.M-power k)
  g-well-defined {₁₊ n} PapR.semi-MR = Derived.lemma-semi-MR n
  g-well-defined PapR.comm-HHSHHS    = PB.axiom RedR.comm-HHSHHS
  g-well-defined PapR.order-CZ       = PB.axiom RedR.order-CZ
  g-well-defined PapR.order-Ex       = PB.axiom RedR.order-Ex
  g-well-defined PapR.comm-CZ-S↑     = PB.axiom RedR.comm-CZ-S↑
  g-well-defined PapR.semi-M↑CZ      = PB.axiom RedR.semi-M↑CZ
  g-well-defined PapR.semi-Ex-S↑     = PB.axiom RedR.semi-Ex-S↑
  g-well-defined PapR.semi-Ex-H↑     = PB.axiom RedR.semi-Ex-H↑
  g-well-defined PapR.blake-c12      = PB.axiom RedR.blake-c12
  g-well-defined PapR.yang-baxter    = PB.axiom RedR.yang-baxter
  g-well-defined PapR.cz-slide       = PB.axiom RedR.cz-slide
  g-well-defined PapR.semi-CX↑-CZ↓   = PB.axiom RedR.semi-CX↑-CZ↓
  g-well-defined (PapR.comm₁ gt w)   = PB.axiom (RedR.comm₁ gt w)
  g-well-defined (PapR.comm₂ gt w)   = PB.axiom (RedR.comm₂ gt w)
  g-well-defined (PapR.cong↑ eq)     = RedR.lemma-cong↑ _ _ (g-well-defined eq)

  -- g lifts to the whole congruence, so every Paper-V1 theorem — and
  -- through Paper-V1.Iso every Paper-V0 one — is a Reduced theorem.
  module _ (n : ℕ) where

    open import Presentation.MorphismId
      (PapR._QRel,_===_ n) (RedR._QRel,_===_ n) using (module Star-Congruence)

    pap⇒red : ∀ {w v} → let open PB (PapR._QRel,_===_ n) using (_≈_) in
              w ≈ v → let open PB (RedR._QRel,_===_ n) renaming (_≈_ to _≈'_) in w ≈' v
    pap⇒red = Star-Congruence.lemma-id*-cong g-well-defined

  ------------------------------------------------------------------------
  -- The theorem
  --
  -- On the Paper-V1 side the grouplike witness is Paper-V1.Iso's, the one
  -- Paper-V1.Presentation builds its word group from, so that the two
  -- isomorphisms compose there.

  module M (n : ℕ) where
    module G1 = Group-Lemmas (RedR._QRel,_===_ n) (red-grouplike {n})
    module G2 = Group-Lemmas (PapR._QRel,_===_ n) (PIso.Theorem.pap-grouplike {n})

    open import Presentation.MorphismId (RedR._QRel,_===_ n) (PapR._QRel,_===_ n)
    open GroupMorphs (red-grouplike {n}) (PIso.Theorem.pap-grouplike {n})

    Theorem-Reduced-iso-PaperV1 :
      IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
    Theorem-Reduced-iso-PaperV1 =
      StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
