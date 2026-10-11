------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1 mod scalars is Paper-V1, hence Paper-V0.
--
-- The two rule sets are relations over the same alphabet, Symplectic's
-- gates, and agree rule for rule except at one place: Paper-V1's
-- semi-MR conjugates S by M_g⁻¹, Figure 1's semi-MS (its C4) by M_g.
-- So, as in Paper-V1.Iso, the isomorphism is the identity on words and
-- the content is the pair of well-definedness proofs; fourteen rules
-- and the structural ones go across by `axiom`, and the fifteenth is
-- SemiMS, run in each direction.
--
-- What clients take from here is the pair of transports
--
--     fq⇒v0 : u ≈ v in Figure 1 mod scalars  →  u ≈ v in Paper-V0
--     v0⇒fq : u ≈ v in Paper-V0              →  u ≈ v in Figure 1 mod scalars
--
-- through which every Paper-V0 theorem — and Paper-V0 is the quotient
-- of the exact presentation — is a theorem of Figure 1 mod scalars, and
-- conversely.
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

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Iso
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Function using (id)

open import Word.Base using (Word ; _•_)
import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Presentation.MorphismId as MId

open Primitive-Root-Modp' g* g-gen using (g′)

-- Figure 1 mod scalars, opened: it re-exports the shared gate layer.
open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Syntactics
  p-3 p-prime g* g-gen
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Lemmas
  p-3 p-prime g* g-gen as FQL
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.SemiMS
  p-3 p-prime g* g-gen as SMS

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen as V1
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas
  p-3 p-prime g* g-gen as V1L
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Iso
  p-3 p-prime g* g-gen as V1Iso
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as V0
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Iso
  p-3 p-prime g* g-gen as V0Iso

module FQR = Clifford-Relations
module V1R = V1.Clifford-Relations
module V0R = V0.Clifford-Relations

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The one rule that differs, in each theory

-- semi-MS, derived in Paper-V1 from its semi-MR.
v1-semi-MS : ∀ n →
             let open PB ((₁₊ n) V1R.QRel,_===_) using (_≈_) in
             V1R.XMg • S ≈ FQR.Z^ SMS.c • (S^ SMS.d • V1R.XMg)
v1-semi-MS n =
  C.MR⇒MS (PB.axiom V1R.semi-MR)
  where
  module C = SMS.Conversion n ((₁₊ n) V1R.QRel,_===_) V1R.XMg
               (PB.axiom V1R.order-S)
               (V1L.One-Wire.lemma-order-Z n)
               (V1L.One-Wire.lemma-comm-Z-S n)
               (λ w → V1L.lemma-pow-mod {₁₊ n} {w})
               (V1L.One-Wire-Group.Z-XM n g′)

-- semi-MR, derived in Figure 1 mod scalars from its semi-MS.
fq-semi-MR : ∀ n →
             let open PB ((₁₊ n) FQR.QRel,_===_) using (_≈_) in
             FQR.XMg • (S^ (g * g) • FQR.Z^ SMS.e) ≈ S • FQR.XMg
fq-semi-MR n =
  C.MS⇒MR (PB.axiom FQR.semi-MS)
  where
  module C = SMS.Conversion n ((₁₊ n) FQR.QRel,_===_) FQR.XMg
               (PB.axiom FQR.order-S)
               (FQL.One-Wire.lemma-order-Z n)
               (FQL.One-Wire.lemma-comm-Z-S n)
               (λ w → FQL.lemma-pow-mod {₁₊ n} {w})
               (FQL.One-Wire-Group.Z-XM n g′)

------------------------------------------------------------------------
-- The isomorphism with Paper-V1

module Theorem where

  -- Figure 1 mod scalars → Paper-V1.
  f-well-defined : ∀ {n} →
    let open PB (n V1R.QRel,_===_) renaming (_≈_ to _≈₂_) in
    ∀ {w v} → n FQR.QRel, w === v → id w ≈₂ id v
  f-well-defined FQR.order-S       = PB.axiom V1R.order-S
  f-well-defined FQR.order-H       = PB.axiom V1R.order-H
  f-well-defined (FQR.M-power k)   = PB.axiom (V1R.M-power k)
  f-well-defined {₁₊ n} FQR.semi-MS = v1-semi-MS n
  f-well-defined FQR.comm-HHSHHS   = PB.axiom V1R.comm-HHSHHS
  f-well-defined FQR.order-CZ      = PB.axiom V1R.order-CZ
  f-well-defined FQR.order-Ex      = PB.axiom V1R.order-Ex
  f-well-defined FQR.comm-CZ-S↑    = PB.axiom V1R.comm-CZ-S↑
  f-well-defined FQR.semi-M↑CZ     = PB.axiom V1R.semi-M↑CZ
  f-well-defined FQR.semi-Ex-S↑    = PB.axiom V1R.semi-Ex-S↑
  f-well-defined FQR.semi-Ex-H↑    = PB.axiom V1R.semi-Ex-H↑
  f-well-defined FQR.blake-c12     = PB.axiom V1R.blake-c12
  f-well-defined FQR.yang-baxter   = PB.axiom V1R.yang-baxter
  f-well-defined FQR.cz-slide      = PB.axiom V1R.cz-slide
  f-well-defined FQR.semi-CX↑-CZ↓  = PB.axiom V1R.semi-CX↑-CZ↓
  f-well-defined (FQR.comm₁ gt w)  = PB.axiom (V1R.comm₁ gt w)
  f-well-defined (FQR.comm₂ gt w)  = PB.axiom (V1R.comm₂ gt w)
  f-well-defined (FQR.cong↑ eq)    = V1R.lemma-cong↑ _ _ (f-well-defined eq)

  -- Paper-V1 → Figure 1 mod scalars.
  g-well-defined : ∀ {n} →
    let open PB (n FQR.QRel,_===_) renaming (_≈_ to _≈₁_) in
    ∀ {u t} → n V1R.QRel, u === t → id u ≈₁ id t
  g-well-defined V1R.order-S       = PB.axiom FQR.order-S
  g-well-defined V1R.order-H       = PB.axiom FQR.order-H
  g-well-defined (V1R.M-power k)   = PB.axiom (FQR.M-power k)
  g-well-defined {₁₊ n} V1R.semi-MR = fq-semi-MR n
  g-well-defined V1R.comm-HHSHHS   = PB.axiom FQR.comm-HHSHHS
  g-well-defined V1R.order-CZ      = PB.axiom FQR.order-CZ
  g-well-defined V1R.order-Ex      = PB.axiom FQR.order-Ex
  g-well-defined V1R.comm-CZ-S↑    = PB.axiom FQR.comm-CZ-S↑
  g-well-defined V1R.semi-M↑CZ     = PB.axiom FQR.semi-M↑CZ
  g-well-defined V1R.semi-Ex-S↑    = PB.axiom FQR.semi-Ex-S↑
  g-well-defined V1R.semi-Ex-H↑    = PB.axiom FQR.semi-Ex-H↑
  g-well-defined V1R.blake-c12     = PB.axiom FQR.blake-c12
  g-well-defined V1R.yang-baxter   = PB.axiom FQR.yang-baxter
  g-well-defined V1R.cz-slide      = PB.axiom FQR.cz-slide
  g-well-defined V1R.semi-CX↑-CZ↓  = PB.axiom FQR.semi-CX↑-CZ↓
  g-well-defined (V1R.comm₁ gt w)  = PB.axiom (FQR.comm₁ gt w)
  g-well-defined (V1R.comm₂ gt w)  = PB.axiom (FQR.comm₂ gt w)
  g-well-defined (V1R.cong↑ eq)    = FQR.lemma-cong↑ _ _ (g-well-defined eq)

  ----------------------------------------------------------------------
  -- Transporting derivations

  module _ (n : ℕ) where

    private
      module FQ→V1 = MId (n FQR.QRel,_===_) (n V1R.QRel,_===_)
      module V1→FQ = MId (n V1R.QRel,_===_) (n FQR.QRel,_===_)
      module V1→V0 = MId (n V1R.QRel,_===_) (n V0R.QRel,_===_)

    fq⇒v1 : ∀ {w v} → PB._≈_ (n FQR.QRel,_===_) w v →
            PB._≈_ (n V1R.QRel,_===_) w v
    fq⇒v1 = FQ→V1.Star-Congruence.lemma-id*-cong f-well-defined

    v1⇒fq : ∀ {w v} → PB._≈_ (n V1R.QRel,_===_) w v →
            PB._≈_ (n FQR.QRel,_===_) w v
    v1⇒fq = V1→FQ.Star-Congruence.lemma-id*-cong g-well-defined

    -- Paper-V1.Iso proves each Paper-V1 axiom in Paper-V0 (its
    -- f-well-defined) and exports the converse transport as v1⇒pap.
    v1⇒v0 : ∀ {w v} → PB._≈_ (n V1R.QRel,_===_) w v →
            PB._≈_ (n V0R.QRel,_===_) w v
    v1⇒v0 = V1→V0.Star-Congruence.lemma-id*-cong
              V1Iso.Theorem.f-well-defined

    fq⇒v0 : ∀ {w v} → PB._≈_ (n FQR.QRel,_===_) w v →
            PB._≈_ (n V0R.QRel,_===_) w v
    fq⇒v0 eq = v1⇒v0 (fq⇒v1 eq)

    v0⇒fq : ∀ {w v} → PB._≈_ (n V0R.QRel,_===_) w v →
            PB._≈_ (n FQR.QRel,_===_) w v
    v0⇒fq eq = v1⇒fq (V1Iso.Theorem.v1⇒pap n eq)

  ----------------------------------------------------------------------
  -- Group-likeness, and the theorem

  fq-grouplike : Grouplike (n FQR.QRel,_===_)
  fq-grouplike = FQL.Paper-GroupLike.grouplike

  open GroupMorphisms

  Theorem-Figure1-ModScalar-iso-PaperV1 : ∀ {n} →
    let module G1 = Group-Lemmas (n FQR.QRel,_===_) (fq-grouplike {n})
        module G2 = Group-Lemmas (n V1R.QRel,_===_) (V1Iso.Theorem.pap-grouplike {n})
    in IsGroupIsomorphism (Group.rawGroup G1.•-ε-group)
                          (Group.rawGroup G2.•-ε-group) id
  Theorem-Figure1-ModScalar-iso-PaperV1 {n} =
    StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
    where
    open MId (n FQR.QRel,_===_) (n V1R.QRel,_===_)
    open GroupMorphs (fq-grouplike {n}) (V1Iso.Theorem.pap-grouplike {n})
