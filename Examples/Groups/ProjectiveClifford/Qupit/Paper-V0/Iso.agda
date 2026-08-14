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
-- Ten axioms are shared verbatim and discharge by `axiom` on the other
-- side:
--
--     order-S  order-H  M-power  semi-MR  order-SH  comm-HHSHHS
--     order-CZ  comm-CZ-S↑  semi-M↑CZ  rel-X↓-CZ
--
-- Simplified-V1's rel-X↑-CZ is nearly an eleventh: Paper-V0 no longer
-- takes it, since the swap derives it from rel-X↓-CZ, so it goes through
-- Paper-V0.Lemmas' lemma-rel-X↑-CZ instead.
--
-- The remaining fifteen are the real mathematics.  Paper-V0 axiomatises
-- the two- and three-wire layer through the swap Ex and the controlled-X,
-- where Simplified-V1 uses Selinger's c10–c15; neither set mentions the
-- other's words at all (Simplified-V1 never writes Ex, CX or CZ02
-- anywhere), so there was nothing to inherit in either direction.
--
-- All fifteen are now theorems, so `Theorem-PaperV0-iso-V1` below is
-- unconditional.  (A `BridgeData` record used to carry whichever of them
-- were still open, the way Qubit.ExactExtension carries ExactData; it is
-- gone.)  The eight Simplified-V1 rules are derived in Paper-V0.Lemmas,
-- and the seven Paper-V0 rules in Simplified-V1.ExRules; the note before
-- `module Theorem` says how each one goes.
--
-- The three-wire rules are the ones Proposition 2.55 bears on.  Both rule
-- sets are extension presentations of Pauli n ⋊ Sp(2n, ℤ/pℤ) over the
-- same kernel, and their three-wire relators are pure symplectic
-- relators — no Pauli content — so they are the R-part of the recipe,
-- lifted along the same section.  That is exactly why they transport:
-- ExRules carries them from the symplectic tree along the morphism that
-- sends the symplectic S to R, and a relator with no S in it is carried
-- to itself.  Simplified-V1.Presentation proves the V1 side presents
-- that group.
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

import Relation.Binary.PropositionalEquality as Eq

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
-- Where the two halves are proved
--
-- Nothing is outstanding; a `BridgeData` record of obligations used to
-- stand here, and the last of its fields is gone.  For the record, where
-- each half now lives:
--
--   * Simplified-V1's axioms, as Paper-V0 theorems — Paper-V0.Lemmas.
--     semi-M↓CZ and comm-CZ-S↓ are the ↑-rules conjugated by the swap.
--     c10 sheds a leading H ↑ off each side (the left by lemma-CZ-H↑,
--     the right by the Euler decomposition of the multiplier by −1) and
--     is then blake-c12's commutator with R for S, the two reconciled by
--     the Pauli-versus-XC rule lemma-conj-XC-Z↑ since R = S • Z ^ ½.
--     c11 is c10 conjugated by the swap.  c12 is the progress report's
--     Lemma 9.  Both sides of c13 are CZ02.  c14 telescopes, because
--     conjugation by ⊤⊥ ↑ sends CZ to CZ02 and CZ02 to the inverse of
--     CZ • CZ02, and ⊤⊥ ↑ has order 3.  c15 is c14 transported along the
--     transposition of wires 0 and 2.
--
--   * Paper-V0's axioms, as Simplified-V1 theorems —
--     Simplified-V1.ExRules.  The five with no S in them are transported
--     from the symplectic tree along Simplified-V1.Forward's f, which
--     sends the symplectic S to R = S • Z ^ ½ and fixes everything else.
--     The two that do mention S come back from that transport in the
--     R-spelling, and the difference is a Pauli: for semi-Ex-S↑ a single
--     Z ^ ½, moved across the swap and cancelled; for blake-c12 four of
--     them, one of which crosses the CX and is doubled onto the other
--     wire, after which each wire's exponent is h • p.

------------------------------------------------------------------------
-- The isomorphism

module Theorem where

  -- f : Paper-V0 → Simplified-V1.
  f-well-defined : ∀ {n} → let open PB (V1R._QRel,_===_ n) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> PapR._QRel,_===_ n w v -> id w ≈₂ id v
  -- The eleven shared axioms.
  f-well-defined PapR.order-S       = PB.axiom V1R.order-S
  f-well-defined PapR.order-H       = PB.axiom V1R.order-H
  -- Not shared: Paper-V0 states these over XMg = XM g′, which is M at the
  -- inverse unit (XM≡M⁻¹), so V1 has to prove them — Simplified-V1.ExRules
  -- does, by cancelling against Mg.  The refl' steps are just the bridge
  -- rewriting XM into M.
  f-well-defined {₁₊ n} (PapR.M-power k) =
    PB.trans (PB.refl' _ (Eq.cong (_^ toℕ k) (PapR.XM≡M⁻¹ g′)))
      (PB.trans (ExR.XM-Rules.lemma-M-power n k)
                (PB.refl' _ (Eq.sym (PapR.XM≡M⁻¹(g^ k)))))
  f-well-defined {₁₊ n} PapR.semi-MR =
    PB.trans (PB.refl' _ (Eq.cong (_• PapR.R^ (g * g)) (PapR.XM≡M⁻¹ g′)))
      (PB.trans (ExR.XM-Rules.lemma-semi-MR n)
                (PB.refl' _ (Eq.sym (Eq.cong (PapR.R •_) (PapR.XM≡M⁻¹ g′)))))
  f-well-defined PapR.order-SH      = PB.axiom V1R.order-SH
  f-well-defined PapR.comm-HHSHHS   = PB.axiom V1R.comm-HHSHHS
  f-well-defined PapR.order-CZ      = PB.axiom V1R.order-CZ
  f-well-defined PapR.comm-CZ-S↑    = PB.axiom V1R.comm-CZ-S↑
  f-well-defined {₂₊ n} PapR.semi-M↑CZ =
    PB.trans (PB.refl' _ (Eq.cong (λ w → w ↑ • CZ^ g) (PapR.XM≡M⁻¹ g′)))
      (PB.trans (ExR.XM-Rules↑.lemma-semi-M↑CZ n)
                (PB.refl' _ (Eq.sym (Eq.cong (λ w → CZ • w ↑) (PapR.XM≡M⁻¹ g′)))))
  -- The seven Paper-V0-only axioms, all proved in Simplified-V1.ExRules.
  f-well-defined {₂₊ n} PapR.order-Ex     = ExR.lemma-order-Ex
  f-well-defined {₂₊ n} PapR.semi-Ex-S↑   = ExR.Ex-S.lemma-semi-Ex-S↑ n
  f-well-defined {₂₊ n} PapR.semi-Ex-H↑   = ExR.lemma-semi-Ex-H↑
  f-well-defined {₂₊ n} PapR.blake-c12    = ExR.Blake.lemma-blake-c12 n
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
  -- Not shared: Paper-V0 states these three over XMg = Mg ⁻¹, and gets
  -- the Mg forms back in One-Wire / Ex-Conjugation.
  g-well-defined {₁₊ n} (V1R.M-power k) = PapL.One-Wire.lemma-M-power n k
  g-well-defined {₁₊ n} V1R.semi-MR     = PapL.One-Wire.lemma-semi-MR n
  g-well-defined V1R.order-SH       = PB.axiom PapR.order-SH
  g-well-defined V1R.comm-HHSHHS    = PB.axiom PapR.comm-HHSHHS
  g-well-defined V1R.order-CZ       = PB.axiom PapR.order-CZ
  g-well-defined V1R.comm-CZ-S↑     = PB.axiom PapR.comm-CZ-S↑
  g-well-defined {₂₊ n} V1R.semi-M↑CZ = PapL.Ex-Conjugation.lemma-semi-M↑CZ n
  -- Not shared: Paper-V0 takes NEITHER Pauli-versus-CZ rule.  The lower
  -- one follows from blake-c12 and the multiplier calculus, and the
  -- upper one is the lower one conjugated by the swap.
  g-well-defined {₂₊ n} V1R.rel-X↑-CZ = PapL.Ex-Conjugation.lemma-rel-X↑-CZ n
  g-well-defined {₂₊ n} V1R.rel-X↓-CZ = PapL.Ex-Conjugation.lemma-rel-X↓-CZ n
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
