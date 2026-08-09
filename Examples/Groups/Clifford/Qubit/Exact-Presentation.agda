------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group *with* its scalar, presented as a group
-- extension (Selinger, arXiv:1310.6813).
--
--     1 ─→ ⟨ω⟩ ≅ ℤ/8 ─→ Exact n ─→ CMS n ─→ 1
--
-- This is the scalar layer, one storey above Qubit.Presentation: there
-- the normal subgroup is the Pauli group and the quotient is symplectic;
-- here the normal subgroup is the centre ⟨ω⟩ and the quotient is the
-- Clifford group modulo scalars.  The group side of the sequence is
-- Qubit.ExactExtension.Exact; what is built here is its presentation,
--
--     extension-presentation S R̄ conj corr
--
-- (Presentation.Construct.Properties.Extension, Proposition 2.55), where
--
--   * S    = the cyclic presentation of order 8, ⟨ ω ∣ ω⁸ = 1 ⟩
--            (Cyclic.Syntactics, whose single generator is renamed ω on
--            import — in this presentation the scalar IS a generator),
--   * R̄    = Selinger's Figure 8 taken modulo scalars
--            (Selinger.Figure8-Mod-Scalar),
--   * conj = the action of a Clifford gate on the scalar: trivial,
--            since ω is central,
--   * corr = the cocycle: the power of ω that a mod-scalar relator picks
--            up when it is lifted back to Figure 8.
--
-- The cocycle.  Exactly three of the fifteen relations differ between
-- Figure 8 and its mod-scalar quotient, and the exponents are the ones
-- already computed in Selinger.ScalarKernel.srel-kernel:
--
--     C4   SHSHSH = 1   (Figure 8: = ω)                corr = ω
--     C10  CZ·H↑·CZ = … (Figure 8 keeps a tail ω⁻¹)    corr = ω⁷
--     C11  the same on the other wire                  corr = ω⁷
--     the other twelve, and comm₁ / comm₂              corr = ε
--
-- cong↑ recurses with the SAME word.  This is where the scalar cocycle
-- is easier than the Pauli one of Qubit.Presentation, which has to shift
-- its correction up a qubit (shiftPauli): the scalar alphabet does not
-- depend on the width, one generator ω naming the scalar on every wire.
-- That is Figure8.cω↑ (ω ↑ = ω) turned into syntax — once ω is a
-- generator rather than the derived word (SH)³, there is nothing left to
-- shift.  For the same reason Figure8.cω (centrality) becomes the single
-- clause of `conj` below.
--
-- Width.  The relation is stated at every width n, which is possible
-- precisely because the scalar has become a generator: nothing here
-- mentions the word (SH)³, so nothing needs a wire to write it on.
--
-- The presentation THEOREM is a different matter, and is to be read at
-- width ₁₊ n, as Qubit.ExactExtension states it.  At width 0 the gate
-- alphabet Gen 0 is empty, so every circuit is ε and the group Figure 8
-- presents is trivial, whereas _Exact, 0 ===_ is ⟨ ω ∣ ω⁸ ⟩ ≅ ℤ/8: the
-- scalar has nowhere to live, and ⟨ω⟩ cannot embed.  Instantiating this
-- relation at ₁₊ n is what the group side wants; indexing it at n costs
-- nothing and keeps the definition uniform.
--
-- The corrections are not all trivial, so this instance is not the split
-- one that Presentation.Construct.Properties.SemiDirectProduct2 covers;
-- the twisted relators are what the extension recipe adds.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Exact-Presentation where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)

open import Word.Base using (Word ; WRel ; ε ; _^_)

open import Presentation.Construct.Properties.Extension
  using (extension-presentation)
open import Presentation.Definitions using (_IsPresentationOf_)

-- The cyclic generator is the scalar, so it is imported under the name
-- Figure 8 gives it.  (Figure8-Mod-Scalar, the other import, defines no
-- ω of its own — modulo scalars there is nothing for it to name.)
-- Re-exported: the scalar alphabet and its generator are part of this
-- module's interface, since _Exact,_===_ is a relation over them.
open import Examples.Groups.Cyclic.Syntactics
  using (_Cn,_===_) renaming (X to ScalarGen ; T to ω) public
import Examples.Groups.Cyclic.Presentation as Cyc
import Examples.Groups.Cyclic.Semantics as CycSem

-- The qubit case, p = 2.  Taken from PrimitiveRoot rather than
-- CliffordGroup: the two agree definitionally, and this one does not go
-- through the P4-action layer.
open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime
  as MS

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- S : the scalars ⟨ω⟩ ≅ ℤ/8
--
-- One generator (Cyclic.Syntactics.X is a singleton), one relation
-- ω⁸ = 1.  Cyclic.Presentation shows this is a presentation of ℤ/8, so
-- the normal factor needs no work of its own here.

Scalar-relation : WRel ScalarGen
Scalar-relation = 8 Cn,_===_

Scalar-presentation : Scalar-relation IsPresentationOf CycSem.Cn-group 8
Scalar-presentation = Cyc.presentation {7}

-- ω⁻¹ = ω⁷, since ω has order 8 (Figure 8's C1, here S's `order`).
-- Right-associated, matching Figure8.ω⁻¹, so that the translation of
-- Qubit.Exact-Iso-CMS carries it across without re-bracketing.
ω⁻¹ : Word ScalarGen
ω⁻¹ = ω ^ 7

------------------------------------------------------------------------
-- conj : the scalar is central
--
-- A gate conjugates the scalar to itself.  That single clause is all the
-- action there is, and it is what makes ⟨ω⟩ normal in the Clifford
-- group; in Figure 8, where ω is the derived word (SH)³, the same fact
-- has to be an axiom (Figure8.cω).

conj : Gen n → ScalarGen → Word ScalarGen
conj _ _ = ω

------------------------------------------------------------------------
-- corr : the scalar cocycle
--
-- corr r is the word w_r of Proposition 2.55: lifting the mod-scalar
-- relator r back to Figure 8 leaves the discrepancy
--
--     [ lhs ]ᵣ  ≈  [ corr r ]ₗ • [ rhs ]ᵣ.
--
-- Its exponents are Selinger.ScalarKernel.srel-kernel's, which proves
-- the corresponding equations in Figure 8 itself; the two must be read
-- together, since that lemma is what makes this definition the right
-- one.  (There the scalar is the word ω and the discrepancy is written
-- on the right, rhs • ωᵏ; centrality moves it across.)

srel-corr : ∀ {u v} → (n MS.Sel, u === v) → Word ScalarGen
srel-corr MS.c4  = ω
srel-corr MS.c10 = ω⁻¹
srel-corr MS.c11 = ω⁻¹
srel-corr _      = ε

corr : ∀ {u v} → (n MS.CRel, u === v) → Word ScalarGen
corr (MS.srel r)    = srel-corr r
corr (MS.cong↑ r)   = corr r
corr (MS.comm₁ h g) = ε
corr (MS.comm₂ h g) = ε

------------------------------------------------------------------------
-- The exact Clifford presentation
--
-- The alphabet is ScalarGen ⊎ Gen n: the scalar ω, and the gates.
-- Unfolding extension-presentation, the relations are
--
--   S    ω⁸ = 1                                     (on the scalar)
--   T    g⁻¹ ω g = ω     for every gate g           (conj, centrality)
--   R    the fifteen Figure-8 relations, each corrected by its power of
--        ω                                          (corr, twisted)
--
-- and nothing else: the gate side contributes EmptyRel, every mod-scalar
-- relation having been twisted into the mixed part.

infix 4 _Exact,_===_

_Exact,_===_ : (n : ℕ) → WRel (ScalarGen ⊎ Gen n)
_Exact,_===_ n =
  extension-presentation Scalar-relation (n MS.CRel,_===_) conj corr

------------------------------------------------------------------------
-- What Proposition 2.55 would still need
--
-- The analogue of Qubit.ExtensionPresentation, one layer up, applied to
-- _Exact, (₁₊ n) ===_ (see the note on width above).  Of the
-- proposition's inputs, the scalar side is done and the quotient side is
-- the open front:
--
--   pN        Scalar-presentation, above;
--   nfpS      Cyclic.Normalization's normal form (nf w = the exponent
--             mod 8) upgraded to a bijection — its codomain is a Fin,
--             so propositional equality is already the right one;
--   et        Qubit.ExactExtension.Exact, given an ExactData.  Its
--             normal factor is bundled as +-0-group 6 rather than
--             Cn-group 8; the two are ℤ/8 with the same carrier and
--             operations, differing only in the packaged IsGroup, so
--             lining them up is bookkeeping;
--   pQ        a presentation of CMS (₁₊ n) by the mod-scalar relations.
--             This is the missing piece, and it is the same one
--             Selinger.Scalars calls Complete-mod-scalars: it needs
--             Qubit.ExtensionPresentation.Clifford.presentation composed
--             with Selinger.Iso;
--   sound-ax  centrality of ω and the three corrected relators, read in
--             the exact group.  Both families exist already, as
--             Figure8.ω-central and Selinger.ScalarKernel.srel-kernel;
--             what is left is to read them through the mixed alphabet,
--             as ExtensionPresentation does with embˡ / embʳ;
--   real-Q    a gate projects to itself, since ExactExtension's proj is
--             the identity on words;
--   Realises  a scalar generator is interpreted as ω, which is
--             ExactExtension's incl at exponent 1;
--   Sec-trivial / Conj-trivial
--             the identity coset's representative is trivial in the
--             exact group.  Conj-trivial is free here, unlike in the
--             Pauli layer: conj is constant, so conjugating ω by any
--             representative returns ω on the nose.
------------------------------------------------------------------------
