{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The id-isomorphism  Paper-V0.Clifford-Relations ≅ Simplified-V1.Clifford-Relations.
--
-- Both rule sets are relations over the SAME alphabet — Symplectic's
-- three gates H, S, CZ — so the candidate isomorphism is the identity on
-- words, exactly as in Simplified-V2.Iso, and the whole content is the
-- pair of well-definedness proofs:
--
--   f-well-defined : every Paper-V0 axiom holds in Simplified-V1;
--   g-well-defined : every Simplified-V1 axiom holds in Paper-V0.
--
-- Eleven axioms are shared verbatim and discharge by `axiom` on the other
-- side:
--
--     order-S  order-H  M-power  semi-MR  order-SH  comm-HHSHHS
--     order-CZ  comm-CZ-S↑  semi-M↑CZ  rel-X↑-CZ  rel-X↓-CZ
--
-- The rest are the real mathematics.  Paper-V0 axiomatises the two- and
-- three-wire layer through the swap Ex and the controlled-X, where
-- Simplified-V1 uses Selinger's c10–c15; neither set mentions the other's
-- words at all (Simplified-V1 never writes Ex, CX or CZ02 anywhere), so
-- there is nothing to inherit in either direction.
--
-- One direction is complete: every Simplified-V1 axiom is derived in
-- Paper-V0.Lemmas.  Of the other direction, the five Paper-V0 rules that
-- do not mention S are derived in Simplified-V1.ExRules, by transporting
-- the symplectic tree's Ex calculus along the morphism that sends the
-- symplectic S to R.  `BridgeData` below is what is left: the two
-- Paper-V0 rules that do mention S, where that transport gives the
-- R-spelling and the difference is a Pauli.
--
-- Why a record rather than holes.  The library is postulate-free and
-- every file typechecks under --safe, so the outstanding derivations are
-- taken as an explicit input, the way Qubit.ExactExtension takes
-- ExactData: `theorem` below is a definition, not a hole, and each field
-- is a precisely stated lemma to be discharged.  Discharging a field is
-- a local edit that cannot silently weaken the theorem.
--
-- The three-wire fields are the ones Proposition 2.55 bears on.  Both
-- rule sets are extension presentations of Pauli n ⋊ Sp(2n, ℤ/pℤ) over
-- the same kernel, and their three-wire relators are pure symplectic
-- relators — no Pauli content — so they are the R-part of the recipe,
-- lifted along the same section.  Simplified-V1.Presentation already
-- proves the V1 side presents that group.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (id)
open import Data.Product using (_,_ ; ∃ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Word.Base using (Word ; _•_ ; ε ; _^_ ; [_]ʷ)
import Presentation.Base as PB
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open GroupMorphisms

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import Notations

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Iso
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The Paper-V0 side is opened unqualified: it re-exports the shared
-- generator layer (Gen, and the derived words S, H, CZ, Ex, CX, CZ02, …),
-- which both rule sets are written over.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  p-3 p-prime g* g-gen as V1
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Lemmas
  p-3 p-prime g* g-gen as V1L
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  p-3 p-prime g* g-gen as PapL
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.ExRules
  p-3 p-prime g* g-gen as ExR

module PapR = Clifford-Relations
module V1R  = V1.Clifford-Relations

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The outstanding derivations
--
-- Group A: the Paper-V0 axioms that Simplified-V1 does not have, stated
-- in Simplified-V1's congruence.  Group B: the Simplified-V1 axioms that
-- Paper-V0 does not have, stated in Paper-V0's congruence.

record BridgeData : Set where
  field
    -- A. Paper-V0's blake-c12, inside Simplified-V1.
    --
    -- This is the last one.  Six of the seven are proved in
    -- Simplified-V1.ExRules, by transporting the symplectic tree's Ex
    -- calculus along Simplified-V1.Forward's f.  That transport is the
    -- identity on any rule with no S in it; f sends the symplectic S to
    -- R = S • Z ^ ½, so a rule that does mention S comes back in the
    -- R-spelling and the difference is a Pauli.  For semi-Ex-S↑ that
    -- Pauli is a single Z ^ ½, which ExRules moves across the swap and
    -- cancels.  blake-c12 carries four of them, two of which have to
    -- cross a CX, and that crossing is not proved yet.
    --
    -- Stated in Word order, matching Paper-V0's corrected axiom; the old
    -- spelling was the circuit-order reading of the same relation.
    v1-blake-c12 :
      ∀ {n} → let open PB (V1R._QRel,_===_ (₂₊ n)) using (_≈_) in
      (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX ≈ CZ

    -- B. Simplified-V1's two- and three-wire axioms, inside Paper-V0.
    --
    -- There are none left.  semi-M↓CZ and comm-CZ-S↓ are proved in
    -- Paper-V0.Lemmas by conjugating their ↑-counterparts with the swap;
    -- so are c10 and c11, and c12–c15 (see below).
    --
    -- selinger-c10 used to sit here; it is now proved in Paper-V0.Lemmas.
    -- Both sides shed a leading H ↑ — the left by lemma-CZ-H↑, the right
    -- by the Euler decomposition of the multiplier by −1 — leaving the
    -- conjugation of R ↑ by XC.  That is blake-c12's commutator with R in
    -- place of S, and the two are reconciled by the Pauli-versus-XC rule
    -- lemma-conj-XC-Z↑, since R = S • Z ^ ½.
    -- selinger-c11 used to sit here; it is c10 conjugated by the swap,
    -- which exchanges the wires and fixes CZ.
    -- selinger-c12 used to sit here; it is now proved in Paper-V0.Lemmas,
    -- by the progress report's Lemma 9.
    -- selinger-c13 used to sit here; it is now proved in Paper-V0.Lemmas.
    -- Both of its sides are CZ02: the half-swaps are involutions, so each
    -- side is a conjugation of a CZ, and the conjugating half-swap is
    -- transparent to it by selinger-c12 and its 3-cycle conjugate.
    -- selinger-c14 used to sit here; it is now proved in Paper-V0.Lemmas.
    -- Conjugation by ⊤⊥ ↑ sends CZ to CZ02 (c13) and CZ02 to the inverse
    -- of CZ • CZ02 (C18), and ⊤⊥ ↑ has order 3, so the cube telescopes.
    -- selinger-c15 used to sit here; it is now proved in Paper-V0.Lemmas,
    -- as c14 transported along the transposition of wires 0 and 2.

------------------------------------------------------------------------
-- The isomorphism

module Theorem (bd : BridgeData) where

  open BridgeData bd

  -- f : Paper-V0 → Simplified-V1.
  f-well-defined : ∀ {n} → let open PB (V1R._QRel,_===_ n) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> PapR._QRel,_===_ n w v -> id w ≈₂ id v
  -- The eleven shared axioms.
  f-well-defined PapR.order-S       = PB.axiom V1R.order-S
  f-well-defined PapR.order-H       = PB.axiom V1R.order-H
  f-well-defined (PapR.M-power k)   = PB.axiom (V1R.M-power k)
  f-well-defined PapR.semi-MR       = PB.axiom V1R.semi-MR
  f-well-defined PapR.order-SH      = PB.axiom V1R.order-SH
  f-well-defined PapR.comm-HHSHHS   = PB.axiom V1R.comm-HHSHHS
  f-well-defined PapR.order-CZ      = PB.axiom V1R.order-CZ
  f-well-defined PapR.comm-CZ-S↑    = PB.axiom V1R.comm-CZ-S↑
  f-well-defined PapR.semi-M↑CZ     = PB.axiom V1R.semi-M↑CZ
  f-well-defined PapR.rel-X↑-CZ     = PB.axiom V1R.rel-X↑-CZ
  f-well-defined PapR.rel-X↓-CZ     = PB.axiom V1R.rel-X↓-CZ
  -- The seven Paper-V0-only axioms: six proved in Simplified-V1.ExRules,
  -- one still taken as input.
  f-well-defined {₂₊ n} PapR.order-Ex     = ExR.lemma-order-Ex
  f-well-defined {₂₊ n} PapR.semi-Ex-S↑   = ExR.Ex-S.lemma-semi-Ex-S↑ n
  f-well-defined {₂₊ n} PapR.semi-Ex-H↑   = ExR.lemma-semi-Ex-H↑
  f-well-defined PapR.blake-c12           = v1-blake-c12
  f-well-defined {₃₊ n} PapR.yang-baxter  = ExR.lemma-yang-baxter
  f-well-defined {₃₊ n} PapR.cz-slide     = ExR.lemma-cz-slide
  f-well-defined {₃₊ n} PapR.semi-CX↑-CZ↓ = ExR.lemma-semi-CX↑-CZ↓
  -- Structural rules.
  -- comm₁ concludes at ₁₊ n and comm₂ at ₂₊ n, so the lowest width of
  -- each is one below what comm-H / comm-S / comm-CZ are stated at.  At
  -- that width the shifted generator is a Gen ₀, which only gate₀
  -- inhabits, and SympGate has no 0-ary gate — so those cases are
  -- vacuous and are discharged by splitting one deeper.
  f-well-defined {₁₊ ₀} (PapR.comm₁ H-gate (gate₀ ()))
  f-well-defined {₁₊ ₀} (PapR.comm₁ S-gate (gate₀ ()))
  f-well-defined {₂₊ ₀} (PapR.comm₂ CZ-gate (gate₀ ()))
  f-well-defined {₂₊ n} (PapR.comm₁ H-gate _)  = PB.axiom V1R.comm-H
  f-well-defined {₂₊ n} (PapR.comm₁ S-gate _)  = PB.axiom V1R.comm-S
  f-well-defined {₃₊ n} (PapR.comm₂ CZ-gate _) = PB.axiom V1R.comm-CZ
  f-well-defined (PapR.cong↑ eq)    = V1R.lemma-cong↑ _ _ (f-well-defined eq)

  -- g : Simplified-V1 → Paper-V0.
  g-well-defined : ∀ {n} → let open PB (PapR._QRel,_===_ n) renaming (_≈_ to _≈₁_) in
    ∀ {u t} -> V1R._QRel,_===_ n u t -> id u ≈₁ id t
  -- The eleven shared axioms.
  g-well-defined V1R.order-S        = PB.axiom PapR.order-S
  g-well-defined V1R.order-H        = PB.axiom PapR.order-H
  g-well-defined (V1R.M-power k)    = PB.axiom (PapR.M-power k)
  g-well-defined V1R.semi-MR        = PB.axiom PapR.semi-MR
  g-well-defined V1R.order-SH       = PB.axiom PapR.order-SH
  g-well-defined V1R.comm-HHSHHS    = PB.axiom PapR.comm-HHSHHS
  g-well-defined V1R.order-CZ       = PB.axiom PapR.order-CZ
  g-well-defined V1R.comm-CZ-S↑     = PB.axiom PapR.comm-CZ-S↑
  g-well-defined V1R.semi-M↑CZ      = PB.axiom PapR.semi-M↑CZ
  g-well-defined V1R.rel-X↑-CZ      = PB.axiom PapR.rel-X↑-CZ
  g-well-defined V1R.rel-X↓-CZ      = PB.axiom PapR.rel-X↓-CZ
  -- The eight Simplified-V1-only axioms.
  g-well-defined {₂₊ n} V1R.semi-M↓CZ  = PapL.Down-Rules.lemma-semi-M↓CZ n
  g-well-defined {₂₊ n} V1R.comm-CZ-S↓ = PapL.Down-Rules.lemma-comm-CZ-S↓ n
  g-well-defined {₂₊ n} V1R.selinger-c10 = PapL.Ex-Conjugation.lemma-selinger-c10 n
  g-well-defined {₂₊ n} V1R.selinger-c11 = PapL.Ex-Conjugation.lemma-selinger-c11 n
  g-well-defined {₃₊ n} V1R.selinger-c12 = PapL.Three-Wire.lemma-selinger-c12 n
  g-well-defined {₃₊ n} V1R.selinger-c13 = PapL.Three-Wire.lemma-selinger-c13 n
  g-well-defined {₃₊ n} V1R.selinger-c14 = PapL.Three-Wire.lemma-selinger-c14 n
  g-well-defined {₃₊ n} V1R.selinger-c15 = PapL.Three-Wire.lemma-selinger-c15 n
  -- Structural rules.
  g-well-defined {₁₊ ₀} (V1R.comm₁ H-gate (gate₀ ()))
  g-well-defined {₁₊ ₀} (V1R.comm₁ S-gate (gate₀ ()))
  g-well-defined {₂₊ ₀} (V1R.comm₂ CZ-gate (gate₀ ()))
  g-well-defined {₂₊ n} (V1R.comm₁ H-gate _)  = PB.axiom PapR.comm-H
  g-well-defined {₂₊ n} (V1R.comm₁ S-gate _)  = PB.axiom PapR.comm-S
  g-well-defined {₃₊ n} (V1R.comm₂ CZ-gate _) = PB.axiom PapR.comm-CZ
  g-well-defined (V1R.cong↑ eq)     = PapR.lemma-cong↑ _ _ (g-well-defined eq)

  ------------------------------------------------------------------------
  -- Group-likeness of the Paper-V0 rules
  --
  -- Transported rather than reproved: g-well-defined lifts to the whole
  -- congruence (Star-Congruence.lemma-id*-cong), so every Simplified-V1
  -- theorem is a Paper-V0 theorem, and in particular each generator keeps
  -- the left inverse Simplified-V1 gives it.

  module _ (n : ℕ) where

    open import Presentation.MorphismId
      (V1R._QRel,_===_ n) (PapR._QRel,_===_ n) using (module Star-Congruence)

    v1⇒pap : ∀ {w v} → let open PB (V1R._QRel,_===_ n) using (_≈_) in
             w ≈ v → let open PB (PapR._QRel,_===_ n) renaming (_≈_ to _≈'_) in w ≈' v
    v1⇒pap = Star-Congruence.lemma-id*-cong g-well-defined

  pap-grouplike : Grouplike (PapR._QRel,_===_ n)
  pap-grouplike {n} x with V1L.Clifford-GroupLike.grouplike {n} x
  ... | w , inv = w , v1⇒pap n inv

  ------------------------------------------------------------------------
  -- The theorem

  module M (n : ℕ) where
    module G1 = Group-Lemmas (PapR._QRel,_===_ n) (pap-grouplike {n})
    module G2 = Group-Lemmas (V1R._QRel,_===_ n) (V1L.Clifford-GroupLike.grouplike {n})

    open import Presentation.MorphismId (PapR._QRel,_===_ n) (V1R._QRel,_===_ n)
    open GroupMorphs (pap-grouplike {n}) (V1L.Clifford-GroupLike.grouplike {n})

    Theorem-PaperV0-iso-V1 :
      IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
    Theorem-PaperV0-iso-V1 =
      StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
