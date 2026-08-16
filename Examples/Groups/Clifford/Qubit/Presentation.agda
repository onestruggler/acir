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
-- The presentation THEOREM is to be read at the same width, and now at
-- every width too, as Qubit.ExactExtension states it.  Width 0 used to
-- be the exception: the SYMPLECTIC alphabet Gen 0 is empty, so the group
-- Figure 8 presented over it was trivial while _Exact, 0 ===_ is
-- ⟨ ω ∣ ω⁸ ⟩ ≅ ℤ/8, and ⟨ω⟩ could not embed.  Once Figure 8 acquired its
-- own gate set the scalar is a 0-ary generator on that side as well, so
-- both sides are ℤ/8 at width 0 and the two agree there — degenerately,
-- the quotient CMS 0 being trivial.
--
-- The corrections are not all trivial, so this instance is not the split
-- one that Presentation.Construct.Properties.SemiDirectProduct covers;
-- the twisted relators are what the extension recipe adds.
--
-- The theorem.  Proposition 2.55 is instantiated at the end of this file
-- (module Exact-Presentation), and the scalar side of it is discharged
-- here: the factor presentation and its bijective normal form, the
-- interpretation, soundness of conj and corr in the exact group, the
-- realisation of a scalar generator, and Conj-trivial — which is free at
-- this layer, conj being constant.  The module still TAKES an ExactData,
-- i.e. ω-faithful, because that is the shape the extension is built
-- with; but it is no longer an assumption, being supplied at every width
-- by the matrix model of Model.Faithful.  `presentation-n` at the foot
-- of this file is the theorem with nothing left to discharge.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Presentation where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Word.Base using (Word ; WRel ; ε ; _^_ ; _•_ ; [_]ʷ ; wmap)

import Presentation.Base as PB
open import Presentation.Construct.Base
  using ([_]ₗ ; [_]ᵣ ; left ; right ; comm)
open import Presentation.Construct.Properties.Extension
  using (extension-presentation ; tw)
import Presentation.Construct.Properties.Extension as Ext
open import Presentation.Definitions using (_IsPresentationOf_)
open import Normalization.NormalForm.Propositional using (BijectiveNormalForm)
import Normalization.NormalForm.Setoid as SNF

open import ForStdlib.Algebra.Construct.Extension using (Extension)

-- The cyclic generator is the scalar, so it is imported under the name
-- Figure 8 gives it.  (Figure8-Mod-Scalar, the other import, defines no
-- ω of its own — modulo scalars there is nothing for it to name.)
-- Re-exported: the scalar alphabet and its generator are part of this
-- module's interface, since _Exact,_===_ is a relation over them.
open import Examples.Groups.Cyclic.Syntactics
  using (_Cn,_===_) renaming (X to ScalarGen ; T to ω) public
import Examples.Groups.Cyclic.Presentation as Cyc
import Examples.Groups.Cyclic.Semantics as CycSem
import Examples.Groups.Cyclic.Normalization as CycN

-- The qubit case, p = 2.  Taken from PrimitiveRoot rather than
-- CliffordGroup: the two agree definitionally, and this one does not go
-- through the P4-action layer.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; Circuit)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime
  as MS

-- The exact side: Figure 8, the dictionary between the two alphabets,
-- the scalar kernel, and the group extension the presentation is of.
import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
import Examples.Groups.Clifford.Qubit.Selinger.Relabel p-2 p-prime as RL
import Examples.Groups.Clifford.Qubit.Selinger.ScalarKernel p-2 p-prime as SK
import Examples.Groups.Clifford.Qubit.ExactExtension as EE
open EE using (_≈ᶠ_)

-- The faithful model, which supplies the ExactData at widths 0 and 1.
import Examples.Groups.Clifford.Qubit.Model.Faithful as Model

-- The quotient: the structural model of the Clifford group mod scalars,
-- which is where ExactExtension's proj lands, and the theorem that the
-- mod-scalar rule set presents it.
open import Examples.Groups.ProjectiveClifford.Qubit.Semantics.VSp
  using (_≈ᵛ_ ; ⟦_⟧ᵛ ; VSp-group)
open import Examples.Groups.ProjectiveClifford.Qubit.Iso2 using (≈ᵛ-refl)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Presentation
  using (presentation-ms ; bijective-ms ; NF-ms-dec)

-- The quotient factor's normal forms: a Pauli vector paired with a
-- symplectic normal form.
open import Data.Product using (_×_)
open import Examples.Groups.Symplectic.Normalization.Boxes p-2 p-prime using (NF)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli)

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
-- Qubit.ExtensionPres-Iso-Figure8 carries it across without
-- re-bracketing.
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
-- nfpS : the scalar factor's bijective normal form
--
-- Proposition 2.55 wants each factor as a BijectiveNormalForm.  For the
-- scalars that is Cyclic.Normalization's — count the generators modulo 8
-- — and the round trip a Bijection needs on top of a NormalForm is
-- f∘g≗id, which the cyclic development already proves.  The codomain is
-- Fin 8, so propositional equality is the right one and nothing has to
-- be transported.  (This is the factor the layer below had to work for:
-- there the quotient's normal forms are records of functions.)

nfpS : BijectiveNormalForm Scalar-relation (CycN.NF 8)
nfpS = record
  { bijection = record
    { to        = CycN.f
    ; cong      = CycN.f-cong
    ; bijective =
        SNF.NormalForm.nf-injective (CycN.nfp' 8)
      , λ u → CycN.g u , λ {z} z≈ →
          Eq.trans (CycN.f-cong z≈) (CycN.f∘g≗id u)
    }
  }

------------------------------------------------------------------------
-- The interpretation of the generators in the exact group
--
-- The exact group's carrier is Figure-8 circuits, so a generator is read
-- as a one-letter word there: the scalar as ω — which on that side is a
-- 0-ary generator, not the word (SH)³ — and a gate as its relabelling,
-- Relabel.sym→ex.  Both are what the translation D undoes.

⟦_⟧₀ : (ScalarGen ⊎ Gen n) → F8.Circuit n
⟦_⟧₀ (inj₁ _) = F8.ω
⟦_⟧₀ (inj₂ g) = [ RL.sym→ex g ]ʷ

-- A word over the scalar alphabet, read in Figure 8.  Since the cyclic
-- alphabet is a singleton, this is just "replace every letter by ω", and
-- on ω ^ k it is F8.ω ^ k on the nose — which is what lines the
-- corrections up with ScalarKernel's exponents below.
scalarWord : Word ScalarGen → F8.Circuit n
scalarWord = wmap (λ _ → F8.gate₀ F8.ω-gate)

------------------------------------------------------------------------
-- Soundness of the cocycle in the exact group
--
-- The correction corr r̄ is the discrepancy left when a mod-scalar
-- relator is lifted to Figure 8, and Selinger.ScalarKernel already
-- computes it — srel-kernel proves exactly these fifteen equations, with
-- the exponents 0 / 1 / 7 that srel-corr copies.  Two things have to be
-- done to its statements.  It writes the scalar on the RIGHT (E u ≈ᶠ
-- E v • ωᵏ), where Proposition 2.55 wants it on the left, so `to-left`
-- moves it across by centrality; and it returns the exponent
-- existentially, so each relator is named here to pin its k down as the
-- one corr picks.

private

  -- The scalar crosses a word, so a correction may be written on either
  -- side.  This is the whole use the extension makes of centrality.
  to-left : {u v : F8.Circuit n} (k : ℕ) →
            u ≈ᶠ (v • SK.Ω n k) → u ≈ᶠ (SK.Ω n k • v)
  to-left {n} k e = PB.trans e (PB.sym (SK.Ω-central n k _))

  -- A scalar word is the same on every wire: Figure8.ω↑≈ω walked across
  -- the word.  This is what lets the cong↑ case below carry a correction
  -- up a wire unchanged, which is the syntactic form of the fact that
  -- the scalar alphabet does not depend on the width.
  scalar-↑ : (c : Word ScalarGen) →
             ((scalarWord {n} c) F8.↑) ≈ᶠ scalarWord c
  scalar-↑ [ _ ]ʷ  = F8.ω↑≈ω
  scalar-↑ ε       = PB.refl
  scalar-↑ (a • b) = PB.cong (scalar-↑ a) (scalar-↑ b)

  -- The fifteen relators, each with the correction srel-corr names.
  -- Eleven are shared with Figure 8 and carry ε; C4 carries ω, C10 and
  -- C11 carry ω⁻¹ = ω⁷.
  srel-sound : {u v : Circuit n} (r : n MS.Sel, u === v) →
               RL.E u ≈ᶠ (scalarWord (srel-corr r) • RL.E v)
  srel-sound MS.c2  = to-left 0 (proj₂ (SK.srel-kernel MS.c2))
  srel-sound MS.c3  = to-left 0 (proj₂ (SK.srel-kernel MS.c3))
  srel-sound MS.c4  = to-left 1 (proj₂ (SK.srel-kernel MS.c4))
  srel-sound MS.c5  = to-left 0 (proj₂ (SK.srel-kernel MS.c5))
  srel-sound MS.c6  = to-left 0 (proj₂ (SK.srel-kernel MS.c6))
  srel-sound MS.c7  = to-left 0 (proj₂ (SK.srel-kernel MS.c7))
  srel-sound MS.c8  = to-left 0 (proj₂ (SK.srel-kernel MS.c8))
  srel-sound MS.c9  = to-left 0 (proj₂ (SK.srel-kernel MS.c9))
  srel-sound MS.c10 = to-left 7 (proj₂ (SK.srel-kernel MS.c10))
  srel-sound MS.c11 = to-left 7 (proj₂ (SK.srel-kernel MS.c11))
  srel-sound MS.c12 = to-left 0 (proj₂ (SK.srel-kernel MS.c12))
  srel-sound MS.c13 = to-left 0 (proj₂ (SK.srel-kernel MS.c13))
  srel-sound MS.c14 = to-left 0 (proj₂ (SK.srel-kernel MS.c14))
  srel-sound MS.c15 = to-left 0 (proj₂ (SK.srel-kernel MS.c15))

  -- ... and the structural rules.  comm₁ / comm₂ are shared verbatim, so
  -- they carry no scalar; cong↑ recurses with the SAME correction, which
  -- is the clause that makes the scalar cocycle easier than the Pauli
  -- one a storey down — there the correction has to be shifted too.
  twisted-sound : {u v : Circuit n} (r̄ : n MS.CRel, u === v) →
                  RL.E u ≈ᶠ (scalarWord (corr r̄) • RL.E v)
  twisted-sound (MS.srel r)    = srel-sound r
  twisted-sound (MS.comm₁ h g) =
    to-left 0 (proj₂ (SK.axiom-kernel (MS.comm₁ h g)))
  twisted-sound (MS.comm₂ h g) =
    to-left 0 (proj₂ (SK.axiom-kernel (MS.comm₂ h g)))
  twisted-sound (MS.cong↑ {w = u} {v = v} r) =
    Eq.subst₂ _≈ᶠ_ (Eq.sym (RL.E-↑ u))
      (Eq.cong (scalarWord (corr r) •_) (Eq.sym (RL.E-↑ v)))
      (PB.trans (F8.lemma-cong↑ _ _ (twisted-sound r))
                (PB.cong (scalar-↑ (corr r)) PB.refl))

------------------------------------------------------------------------
-- Proposition 2.55, instantiated at the scalar layer
--
-- What is supplied here: the scalar side entire (pN, nfpS), the
-- interpretation ⟦_⟧₀, the extension itself (ExactExtension.Exact, given
-- an ExactData), soundness of conj and corr, Realises, and Conj-trivial.
--
-- ONE input is still taken:
--
--   d      an ExactData, which is now a one-field record: ω has order
--          exactly 8 in the presented group.  Its two companions are
--          theorems — soundness is Selinger.Soundness.sound and
--          `scalars` is ExactExtension.scalars — but this one is
--          model-theoretic, and not merely unproved: no abelian
--          invariant can give it (C2 and C3 force 2h = 4s = 0, so
--          3(s+h) = 1 is unsolvable), the P4-action is blind to the
--          scalar by construction (action-blind), and the coset route is
--          circular, Reidemeister–Schreier's left-embedding
--          faithfulness being ω-faithful itself.  It wants matrices over
--          ℤ[1/√2, i] — and it now has them, reduced modulo 17
--          (Model.Faithful), at every width.  So the input is supplied
--          rather than assumed, and presentation-n below is
--          unconditional.
--
-- The quotient presentation is not among them: it is
-- Selinger.Presentation.presentation-ms, assembled from
-- ProjectiveClifford.Qubit.Presentation.presentation-n and Selinger.Iso.
-- Because its interpretation is the VSp denotation itself, the
-- realisation condition Real-Q holds by computation — a gate's
-- projection is D of its relabelling, and Relabel.D∘E says that is the
-- gate.
--
-- Nor is the quotient factor's BIJECTIVE normal form, which used to be
-- the input with nothing behind it.  It is now
-- Selinger.Presentation.bijective-ms, on Pauli n × NF n: the layer below
-- is itself an extension, so Normalization.Construction.bijective builds
-- a normal form for it out of its two factors' — the Pauli one and the
-- symplectic one — and Construction.transport carries that across the
-- mixed alphabet along Selinger.Iso's translation g.  Its normal forms
-- are Vecs, Fins and one symplectic box, hence decidable (NF-ms-dec),
-- which is what the section-fixing below needs.
--
-- Sec-trivial is not among them either.  It cannot be proved of an arbitrary
-- section — and is not merely unproved but false for a bad one, since a
-- representative like (SH)³ is trivial mod scalars while lifting to ω —
-- so the section is fixed instead: NormalForm.Setoid.ε-section replaces
-- the identity coset's representative by ε, which is legitimate because
-- a Bijection's section comes from its surjectivity field and ε
-- discharges that field's obligation there by nf-cong.  This is the same
-- move that settled the layer below.

module Exact-Presentation
  (n : ℕ)
  (d : EE.ExactData n)
  where

  -- The quotient factor's normal form, with its section fixed at the
  -- identity: same map, same congruence, same injectivity, different
  -- representative for the one coset that matters.
  private
    NFQ : Set
    NFQ = Pauli n × NF n

    nfpQ-ε : BijectiveNormalForm (n MS.CRel,_===_) NFQ
    nfpQ-ε = SNF.ε-section (n MS.CRel,_===_) (Eq.setoid NFQ)
               (bijective-ms n) (NF-ms-dec n)

  open module EP = Ext.Presentation
    Scalar-relation (n MS.CRel,_===_) conj corr
    EE.Scalar-group (VSp-group n) (EE.Exact d)
    Scalar-presentation (presentation-ms n)
    ⟦_⟧₀ nfpS nfpQ-ε
    public

  ------------------------------------------------------------------
  -- The two embeddings
  --
  -- ⟦_⟧ is the monoid extension of ⟦_⟧₀ into the exact group, whose
  -- product IS concatenation, so both embeddings are structural: a
  -- right-embedded word is its relabelling E, a left-embedded one is
  -- its scalar reading.

  private
    embʳ : (w : Circuit n) → ⟦ [ w ]ᵣ ⟧ ≡ RL.E w
    embʳ [ g ]ʷ  = Eq.refl
    embʳ ε       = Eq.refl
    embʳ (w • v) = Eq.cong₂ _•_ (embʳ w) (embʳ v)

    embˡ : (c : Word ScalarGen) → ⟦ [ c ]ₗ ⟧ ≡ scalarWord c
    embˡ [ y ]ʷ  = Eq.refl
    embˡ ε       = Eq.refl
    embˡ (c • e) = Eq.cong₂ _•_ (embˡ c) (embˡ e)

  ------------------------------------------------------------------
  -- sound-ax
  --
  -- Two clauses.  The conjugation family is centrality — on the
  -- Figure-8 side ω is 0-ary, so ω-central is Circuit.Base's structural
  -- comm₀ walked across a word, and no axiom of the rule set is used at
  -- all.  The twisted family is twisted-sound above.

  sound-ax : {w v : Word (ScalarGen ⊎ Gen n)} →
             Ext.extp Scalar-relation (n MS.CRel,_===_) conj corr w v →
             Group._≈_ (EE.Exact-group n) ⟦ w ⟧ ⟦ v ⟧
  sound-ax (left (comm y x)) = PB.sym (F8.ω-central [ RL.sym→ex x ]ʷ)
  sound-ax (right (tw {u} {v} r̄))
    rewrite embʳ u | embˡ (corr r̄) | embʳ v = twisted-sound r̄

  ------------------------------------------------------------------
  -- Realises and Conj-trivial
  --
  -- The scalar generator is interpreted as ω, and the extension's incl
  -- at exponent 1 is ω ^ 1, which is ω on the nose.

  realises : Realises
  realises _ = PB.refl

  -- Conjugating a scalar generator by ANY word gives it back: conj is
  -- constant, and the scalar alphabet is a singleton, so each letter of
  -- the acting word rewrites [ x ]ʷ to itself.  This is the one input
  -- the Pauli layer had to work for and this one does not — and it does
  -- not depend on which representative the section picks.
  private
    conjss-scalar : (w : Circuit n) (x : ScalarGen) →
                    conjss w [ x ]ʷ ≡ [ x ]ʷ
    conjss-scalar [ g ]ʷ  x = Eq.refl
    conjss-scalar ε       x = Eq.refl
    conjss-scalar (w • v) x rewrite conjss-scalar v x = conjss-scalar w x

  conj-trivial : Conj-trivial
  conj-trivial x = PB.refl' Scalar-relation (conjss-scalar (rep Iᶜ) x)

  ------------------------------------------------------------------
  -- Sec-trivial
  --
  -- The section was fixed at the identity, so rep Iᶜ is ε on the nose
  -- and there is nothing left to lift: [ ε ]ᵣ is ε, and no correction
  -- can accumulate along a derivation that is not there.  Note the
  -- decision procedure does not reduce here — nf ε is stuck at an
  -- abstract nfpQ — and does not need to.

  sec-trivial : Sec-trivial
  sec-trivial = PB.refl' (_Exact,_===_ n) (Eq.cong [_]ᵣ rep-ε)
    where
    rep-ε : rep Iᶜ ≡ ε
    rep-ε = SNF.ε-section-rep (n MS.CRel,_===_) (Eq.setoid NFQ)
              (bijective-ms n) (NF-ms-dec n)

  ------------------------------------------------------------------
  -- Real-Q
  --
  -- A gate's projection is D of its relabelling, and D undoes the
  -- relabelling on the nose (Relabel.D∘E); the quotient presentation
  -- reads the same gate as its own VSp denotation, since that IS its
  -- interpretation.  So both sides are ⟦ [ x ]ʷ ⟧ᵛ.

  real-Q : ∀ x → Group._≈_ (VSp-group n) (proj ⟦ inj₂ x ⟧₀) ⟦ [ x ]ʷ ⟧Q
  real-Q x =
    Eq.subst (λ w → ⟦ w ⟧ᵛ ≈ᵛ ⟦ [ x ]ʷ ⟧ᵛ)
             (Eq.sym (RL.D∘E [ x ]ʷ))
             (≈ᵛ-refl ⟦ [ x ]ʷ ⟧ᵛ)

  ------------------------------------------------------------------
  -- The presentation theorem

  presentation : (_Exact,_===_ n) IsPresentationOf (EE.Exact-group n)
  presentation = dpres realises sound-ax sec-trivial conj-trivial real-Q

------------------------------------------------------------------------
-- The headline, with every input named

presentation : ∀ {n} (d : EE.ExactData n) →
               (_Exact,_===_ n) IsPresentationOf (EE.Exact-group n)
presentation {n} d = Exact-Presentation.presentation n d

------------------------------------------------------------------------
-- ... and with no input at all
--
-- Model.Faithful reads an n-qubit Clifford circuit as a 2ⁿ × 2ⁿ matrix
-- over ℤ/17ℤ — the defining representation with its coefficients reduced
-- at a prime above 17, where i, √2 and ω all survive and ω has order
-- exactly 8.  That discharges ω-faithful, hence the whole ExactData, at
-- every width, so the presentation theorem for the exact Clifford group
-- has no hypotheses left.

exact-data : ∀ n → EE.ExactData n
exact-data = Model.exact-data

presentation-n : ∀ n → (_Exact,_===_ n) IsPresentationOf (EE.Exact-group n)
presentation-n n = presentation (exact-data n)
