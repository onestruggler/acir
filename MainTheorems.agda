------------------------------------------------------------------------
-- Presentations of groups
--
-- Index of the paper formalizations: the main theorem of each paper
--
-- One section per source, in the order of the corpus table of the
-- OOPSLA draft (oopsla/sections/corpus.tex): groups of two-level
-- matrices, then circuits, then minimality.  Each section re-states the
-- paper's final result with its full type, the relation set and the
-- group it presents imported openly from the development, and proves it
-- by reference to the module named in the banner, so this file is also
-- a reading guide.  A presentation (_IsPresentationOf_) says that the
-- relations present the whole group; a sub-presentation
-- (_IsSubPresentationOf_) that they present the subgroup the
-- generators generate, which for circuits is the group the paper is
-- about.  The intermediate results of each development — normal forms,
-- auxiliary equations, the layers of the qudit Clifford chain — are in
-- its own folder and its README; nothing here rests on a postulate.
--
-- The root reaches every paper formalization, about 1,600 modules, so
-- from scratch it is checked module by module (CLAUDE.md).  The
-- library's other contents — the symmetric, trivial and cyclic groups,
-- the wreath product, the amalgamations, Circuit.Independence — are
-- reached only where a development uses them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module MainTheorems where

open import Algebra.Bundles using (Group)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (ℕ ; 2+ ; _≤_ ; _^_ ; suc)
import Data.Nat as ℕ
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_×_ ; _,_ ; ∃)
open import Function.Bundles using (Inverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Negation using (¬_)

open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Notations using (₁₊ ; ₂₊)
open import ForStdlib.Data.Fin.Mod using (ℤ ; ℤ* ; _^′_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat using (module PrimeModulus')
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)
import Examples.Groups.Qupit-Phase-Affine.Field as Field
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_)

------------------------------------------------------------------------
-- Groups of two-level matrices
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Greylyn (2014): U₄(ℤ[1/√2, i]), the two-qubit Clifford+T operators
--
-- Home: Examples.Groups.Clifford+T-2qubit-TwoLevel.Presentation.  The
-- two-level generators ω_[a], H_[a,b], X_[a,b] and Greylyn's relations
-- present Uₙ(ℤ[1/√2, i]) for n ≤ 4, by the main lemma of the exact
-- synthesis algorithm, as the thesis does.

module Greylyn where

  open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics using (_===_)
  open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)
  import Examples.Groups.Clifford+T-2qubit-TwoLevel.Presentation as P

  presentation : ∀ {n} → n ≤ 4 → (_===_ {n}) IsPresentationOf (U n)
  presentation n≤4 = P.presentation n≤4

------------------------------------------------------------------------
-- Bian and Selinger (2021): Uₙ(ℤ[½, i])
--
-- Home: Examples.Groups.Clifford+CS-TwoLevel.Presentation.  The
-- two-level generators and the relations of their Figure 1 present
-- Uₙ(ℤ[½, i]) in every dimension.

module Bian-Selinger-Un where

  open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics using (_===_)
  open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (U)
  import Examples.Groups.Clifford+CS-TwoLevel.Presentation as P

  presentation : ∀ {n} → (_===_ {n}) IsPresentationOf (U n)
  presentation = P.presentation

------------------------------------------------------------------------
-- Li, Ross and Selinger (2021): Oₙ(ℤ[½]) and Lₙ
--
-- Homes: Examples.Groups.CCX+HH-TwoLevel.Presentation and .Scaled.
-- Presentation.  (−1)_[a], X_[a,b], K_[a,b,c,d] and Table 1 present
-- Oₙ(ℤ[½]) in every dimension (Theorem 4.10), and with I ⊗ H and Table
-- 2 the scaled dyadic orthogonal matrices Lₙ, for n = 2(k + 1)
-- (Theorem 5.7).

module Li-Ross-Selinger where

  open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (_===_)
  open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (O)
  open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics using (_===ᴸ_)
  import Examples.Groups.CCX+HH-TwoLevel.Presentation as P
  import Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation as PL

  presentation : ∀ {n} → (_===_ {n}) IsPresentationOf (O n)
  presentation = P.presentation

  presentationᴸ : ∀ k → (_===ᴸ_ {suc k ℕ.* 2}) IsPresentationOf (PL.L k)
  presentationᴸ k = PL.presentation k

------------------------------------------------------------------------
-- Fang, Heunen and Kaarsgaard (2026), Hadamard-Π: Oₙ(ℤ[1/√2])
--
-- Homes: Examples.Groups.Real-Clifford+CH-TwoLevel.Presentation and
-- Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Presentation.
-- Z_[a], X_[a,b], H_[a,b] and the relations (a1)–(d4) of Figure 6
-- present Oₙ(ℤ[1/√2]) in every dimension.  The paper's proof does not
-- cover one case of its Main Lemma (its Lemmas A.16 and A.17 are
-- false); the development proves the theorem from that case, Hard, and
-- the case itself after Clément's thesis (below).

module Hadamard-Pi where

  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (_===_)
  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (O)
  import Examples.Groups.Real-Clifford+CH-TwoLevel.MainLemma as ML
  import Examples.Groups.Real-Clifford+CH-TwoLevel.Presentation as P
  import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Presentation as C

  -- The paper's proof, given the case it misses ...
  presentation-given : ∀ {n} → ML.Hard {n} → (_===_ {n}) IsPresentationOf (O n)
  presentation-given = P.presentation

  -- ... and the theorem.
  presentation : ∀ {n} → (_===_ {n}) IsPresentationOf (O n)
  presentation = C.presentation

------------------------------------------------------------------------
-- Clément (2019, thesis): Oₙ(ℤ[1/√2]) by relations (1)–(21)
--
-- Home: Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.
-- Presentation.  Clément's own proof, over his version of the
-- synthesis algorithm: his relations, and Figure 6, present Oₙ(ℤ[1/√2])
-- in every dimension.

module Clement-Thesis where

  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (_===_)
  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement using (_===ᶜ_)
  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (O)
  import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Presentation as T

  presentationᶜ : ∀ {n} → (_===ᶜ_ {n}) IsPresentationOf (O n)
  presentationᶜ = T.presentationᶜ

  presentation : ∀ {n} → (_===_ {n}) IsPresentationOf (O n)
  presentation = T.presentation

------------------------------------------------------------------------
-- Circuits
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Selinger (2015): n-qubit Clifford circuits
--
-- Home: Examples.Groups.Qubit-Clifford.Presentation.DOmega.  The gates
-- ω, H, S, CZ and the relations C1–C15 of Figure 8 present the group
-- the circuits on n wires generate in U_{2ⁿ}(𝔻[ω]), at every width.

module Selinger-Clifford where

  open import Examples.Groups.Qubit-Clifford.Syntactics using (_VRel,_===_)
  open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)
  import Examples.Groups.Qubit-Clifford.Presentation.DOmega as P

  presentation : ∀ {n} → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
  presentation = P.presentation

------------------------------------------------------------------------
-- Bian et al. (2026): qudit Clifford circuits, odd prime p
--
-- Homes: Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Presentation
-- and its sources (the symplectic normal form, the projective chain of
-- ProjectiveClifford.Qupit, Qupit-Clifford).  The gates −ω, H, S, CZ
-- and the rules C0–C15 of Figure 1 present the qudit Clifford group at
-- every width: the paper's Theorem 4.10, against the algebraic model,
-- the central extension of Pauli ⋊ Sp(2n, ℤ/pℤ) by ⟨ω⟩ (the Weyl
-- cocycle) times ⟨−1⟩.  The rules name a primitive root g of ℤ/pℤ.

module Qudit-Clifford
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (2+ p-2))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x Eq.≡ g ^′ toℕ k)
  where

  open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics p-3 p-prime g* g-gen
    using (_F,_===_)
  open import Examples.Groups.Clifford+MinusOne.Qupit.Semantics p-3 p-prime g* g-gen
    using (Clifford±)
  import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Presentation p-3 p-prime g* g-gen as P

  figure1-presentation : ∀ n → (n F,_===_) IsPresentationOf (Clifford± n)
  figure1-presentation = P.presentation-Figure1

------------------------------------------------------------------------
-- Makary, Ross and Selinger (2021): real stabilizer circuits
--
-- Homes: Examples.Groups.Real-Clifford.Presentation.DOmega and
-- .DRootTwo.  The gates −1, H, Z, CZ and the relations R1–R16 of Figure
-- 1 present the group the circuits generate, at every width, in
-- U_{2ⁿ}(𝔻[ω]) and in O_{2ⁿ}(ℤ[1/√2]).

module Makary-Ross-Selinger where

  open import Examples.Groups.Real-Clifford.Syntactics using (_VRel,_===_)
  open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)
  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (O)
  import Examples.Groups.Real-Clifford.Presentation.DOmega as PU
  import Examples.Groups.Real-Clifford.Presentation.DRootTwo as PO

  presentation : ∀ {n} → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
  presentation = PU.presentation

  presentationᴼ : ∀ {n} → (n VRel,_===_) IsSubPresentationOf O (2 ^ n)
  presentationᴼ = PO.presentation

------------------------------------------------------------------------
-- Amy, Chen and Ross (2018): CNOT-dihedral circuits
--
-- Home: Examples.Groups.CNOT+Dihedral.Presentation.  The gates ω, X, T,
-- CNOT and the relations R₁–R₁₃ of Figure 1, with the swap rules,
-- present the group the circuits generate in U_{2ⁿ}(𝔻[ω]), at every
-- width.

module Amy-Chen-Ross where

  open import Examples.Groups.CNOT+Dihedral.Syntactics using (_VRel,_===_)
  open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)
  import Examples.Groups.CNOT+Dihedral.Presentation as P

  presentation : ∀ {n} → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
  presentation = P.presentation

------------------------------------------------------------------------
-- Blake (2026): phase-affine circuits in prime dimension p
--
-- Homes: Examples.Groups.Qupit-Phase-Affine.Presentation.Aff, .Lin,
-- .Quad and .Cube.  The four levels — affine circuits, then phases,
-- then S (p odd), then T (p > 3) — each present the group their
-- circuits generate in U_{pⁿ}, over any commutative ring with an
-- involution and an injective character of 𝔽_p: Theorem 1 and its
-- three extensions.

module Blake-Phase-Affine
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2))
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (phase : Field.F p-2 p-prime → A)
  (phase-+ : ∀ a b → phase (Field._+_ p-2 p-prime a b) ≡ phase a * phase b)
  (phase-unit : ∀ a → adj (phase a) * phase a ≡ 1#)
  (phase-injective : ∀ a b → phase a ≡ phase b → a ≡ b)
  where

  open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime using (p)
  open import Examples.Groups.Qupit-Phase-Affine.Matrix p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective
    using (U)
  import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 0 as S₀
  import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 1 as S₁
  import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 2 as S₂
  import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 3 as S₃
  import Examples.Groups.Qupit-Phase-Affine.Presentation.Aff p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective as Aff
  import Examples.Groups.Qupit-Phase-Affine.Presentation.Lin p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective as Lin

  affine-presentation : ∀ {n} → S₀._VRel,_===_ n IsSubPresentationOf U (p ^ n)
  affine-presentation = Aff.presentation

  linear-phase-presentation : ∀ {n} → S₁._VRel,_===_ n IsSubPresentationOf U (p ^ n)
  linear-phase-presentation = Lin.presentation

  module Quadratic (odd : 1 ≤ p-2) where

    import Examples.Groups.Qupit-Phase-Affine.Presentation.Quad p-2 p-prime odd isCR adjI phase phase-+ phase-unit phase-injective as Quad

    quadratic-phase-presentation : ∀ {n} → S₂._VRel,_===_ n IsSubPresentationOf U (p ^ n)
    quadratic-phase-presentation = Quad.presentation

  module Cubic (gt3 : 2 ≤ p-2) where

    import Examples.Groups.Qupit-Phase-Affine.Presentation.Cube p-2 p-prime gt3 isCR adjI phase phase-+ phase-unit phase-injective as Cube

    cubic-phase-presentation : ∀ {n} → S₃._VRel,_===_ n IsSubPresentationOf U (p ^ n)
    cubic-phase-presentation = Cube.presentation

------------------------------------------------------------------------
-- Bian and Selinger (2023): two-qubit Clifford+T circuits
--
-- Homes: Examples.Groups.Clifford+T-2qubit.Presentation and
-- .Circuits.Presentation.  The relations of Figure 1 present the
-- two-qubit Clifford+T group in U₄(ℤ[1/√2, i]), over the paper's
-- alphabet and as circuits over Circuit.Base on two wires.

module Bian-Selinger-Clifford+T where

  open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
  open Clifford+T using (Rel)
  import Examples.Groups.Clifford+T-2qubit.Circuits.Syntactics as C
  open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)
  import Examples.Groups.Clifford+T-2qubit.Presentation as P
  import Examples.Groups.Clifford+T-2qubit.Circuits.Presentation as PC

  presentation : Rel IsSubPresentationOf U 4
  presentation = P.presentation

  circuit-presentation : C._VRel,_===_ 2 IsSubPresentationOf U 4
  circuit-presentation = PC.presentation

------------------------------------------------------------------------
-- Bian and Selinger (2023): three-qubit Clifford+CS circuits
--
-- Homes: Examples.Groups.Clifford+CS-3qubit.Presentation and
-- .Circuits.Presentation.  The relations of Figure 2 present the
-- three-qubit Clifford+CS group in U₈(ℤ[½, i]), over the paper's
-- alphabet and as circuits over Circuit.Base on three wires.

module Bian-Selinger-Clifford+CS where

  open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module CliffordCS)
  open CliffordCS using (Rel)
  import Examples.Groups.Clifford+CS-3qubit.Circuits.Syntactics as C
  open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (U)
  import Examples.Groups.Clifford+CS-3qubit.Presentation as P
  import Examples.Groups.Clifford+CS-3qubit.Circuits.Presentation as PC

  presentation : Rel IsSubPresentationOf U 8
  presentation = P.presentation

  circuit-presentation : C._VRel,_===_ 3 IsSubPresentationOf U 8
  circuit-presentation = PC.presentation

------------------------------------------------------------------------
-- Clément (2026): real Clifford+CH circuits
--
-- Home: Examples.Groups.Real-Clifford+CH.Presentation.  The gates H, Z,
-- CZ, CH and the relations of Figure 4 present the group the circuits
-- on n wires generate in O_{2ⁿ}(ℤ[1/√2]), at every width: Theorem 8.9,
-- with Theorem 4.4, which the paper imports from Hadamard-Π, proved
-- from Clément's thesis.

module Clement-Real-Clifford+CH where

  open import Examples.Groups.Real-Clifford+CH.Syntactics using (_VRel,_===_)
  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (O)
  import Examples.Groups.Real-Clifford+CH.Presentation as P

  presentation : ∀ n → (n VRel,_===_) IsSubPresentationOf O (2 ^ n)
  presentation = P.subpresentationᴼ

------------------------------------------------------------------------
-- Amy, Ross and Wesley (2024): three-qubit Toffoli-Hadamard circuits
--
-- Homes: Examples.Groups.CCX+HH-3qubit.Repaired.Presentation and
-- .Circuits.Presentation.  The relations of Figures 4, 7 and 8,
-- corrected and with the definition of K that Section 5.5 uses but the
-- figures omit, present L₈, the group of 3-qubit Toffoli-Hadamard
-- operators (scaled dyadic orthogonal 8 × 8 matrices), over the paper's
-- alphabet and as circuits over Circuit.Base on three wires.

module Amy-Ross-Wesley where

  open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics using (_===_)
  import Examples.Groups.CCX+HH-3qubit.Circuits.Syntactics as C
  open import Examples.Groups.CCX+HH-3qubit.Repaired.Presentation using (ToffoliHadamard)
  import Examples.Groups.CCX+HH-3qubit.Repaired.Presentation as P
  import Examples.Groups.CCX+HH-3qubit.Circuits.Presentation as PC

  presentation : _===_ IsPresentationOf ToffoliHadamard
  presentation = P.presentation

  circuit-presentation : C._VRel,_===_ 3 IsPresentationOf ToffoliHadamard
  circuit-presentation = PC.presentation

------------------------------------------------------------------------
-- Li, Mosca, Ross, van de Wetering and Zhao (2025): qutrit Clifford
-- circuits
--
-- Home: Examples.Groups.Qutrit-Clifford.Presentation.  The gates −ω, H,
-- S, CZ and the rules C1–C18 of Figure 1 present the n-qutrit Clifford
-- group — the values the circuits denote, exact scaled matrices over
-- ℤ[ζ₁₂] — at every width, and that group has order 6 · ∏ₖ₌₁ⁿ
-- 3 (9ᵏ − 1) 9ᵏ.

module Li-Mosca-Ross-vandeWetering-Zhao where

  open import Examples.Groups.Qutrit-Clifford.Syntactics using (_VRel,_===_)
  open import Examples.Groups.Qutrit-Clifford.Presentation using (Clifford)
  open import Examples.Groups.Qutrit-Clifford.Count using (order)
  import Examples.Groups.Qutrit-Clifford.Presentation as P

  presentation : ∀ n → (n VRel,_===_) IsPresentationOf Clifford n
  presentation = P.presentationᴳ

  clifford-order : ∀ n → Inverse (Group.setoid (Clifford n)) (Eq.setoid (Fin (order n)))
  clifford-order = P.clifford-group-order

------------------------------------------------------------------------
-- Minimality
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Blake (2026): simpler presentations for six fragments
--
-- Home: Examples.Independence.Theorems.  For each fragment — qubit
-- Clifford (Cliff₂), real Clifford (RCliff₂), qutrit Clifford (Cliff₃),
-- Clifford+T (CliffT₂), Clifford+CS (CliffCS₂), CNOT-dihedral
-- (CNOTdihe₂) — the rule set is complete (Theorem 22, by transfer from
-- the presentations above, in the paper's ranges of widths) and no rule
-- follows from the others (Theorem 37, by separating models), so each
-- rule is necessary for completeness: a minimal complete presentation
-- of the matrix semantics.  CliffCS₂ is moreover complete for Clifford
-- circuits at every width, deriving Cliff₂.

module Blake-Minimality where

  import Examples.Independence.Clifford.Syntactics       as Cliff
  import Examples.Independence.Real-Clifford.Syntactics  as RCliff
  import Examples.Independence.Qutrit-Clifford.Syntactics as Cliff3
  import Examples.Independence.Clifford+T.Syntactics     as CliffT
  import Examples.Independence.Clifford+CS.Syntactics    as CliffCS
  import Examples.Independence.CNOT-Dihedral.Syntactics  as CNOTdihe
  import Examples.Independence.Clifford.Semantics        as Cliff-Sem
  import Examples.Independence.Real-Clifford.Semantics   as RCliff-Sem
  import Examples.Independence.Qutrit-Clifford.Semantics as Cliff3-Sem
  import Examples.Independence.Clifford+T.Semantics      as CliffT-Sem
  import Examples.Independence.Clifford+CS.Semantics     as CliffCS-Sem
  import Examples.Independence.CNOT-Dihedral.Semantics   as CNOTdihe-Sem
  open import Examples.Independence.Clifford+CS.CliffordCircuits using () renaming (Φ to Cliff→CliffCS)
  import Examples.Independence.Theorems as T

  Cliff₂-minimal-complete :
    (∀ {n} {w v : Cliff.Circuit n} →
       Cliff-Sem.⟦ w ⟧ Cliff-Sem.≈ Cliff-Sem.⟦ v ⟧ → n Cliff.⊢ w ≈ v) ×
    (∀ {n} {w v : Cliff.Circuit n} (ρ : Cliff._SRel,_===_ n w v) →
       ¬ T.Cliff-M.Complete-without ρ n)
  Cliff₂-minimal-complete = T.Cliff₂-minimal-complete

  RCliff₂-minimal-complete :
    (∀ {n} {w v : RCliff.Circuit n} →
       RCliff-Sem.⟦ w ⟧ RCliff-Sem.≈ RCliff-Sem.⟦ v ⟧ → n RCliff.⊢ w ≈ v) ×
    (∀ {n} {w v : RCliff.Circuit n} (ρ : RCliff._SRel,_===_ n w v) →
       ¬ T.RCliff-M.Complete-without ρ n)
  RCliff₂-minimal-complete = T.RCliff₂-minimal-complete

  Cliff₃-minimal-complete-upto-2 :
    (∀ {n} {w v : Cliff3.Circuit n} →
       Cliff3-Sem.⟦ w ⟧ Cliff3-Sem.≈ Cliff3-Sem.⟦ v ⟧ → n Cliff3.⊢ w ≈ v) ×
    (∀ {n} {w v : Cliff3.Circuit n} (ρ : Cliff3._SRel,_===_ n w v) →
       n ≤ 2 → ¬ T.Cliff3-M.Complete-without ρ n)
  Cliff₃-minimal-complete-upto-2 = T.Cliff₃-minimal-complete-upto-2

  CliffT₂-minimal-complete-upto-1 :
    (∀ {n} {w v : CliffT.Circuit n} → n ≤ 2 →
       CliffT-Sem.⟦ w ⟧ CliffT-Sem.≈ CliffT-Sem.⟦ v ⟧ → n CliffT.⊢ w ≈ v) ×
    (∀ {n} {w v : CliffT.Circuit n} (ρ : CliffT._SRel,_===_ n w v) →
       n ≤ 1 → ¬ T.CliffT-M.Complete-without ρ n)
  CliffT₂-minimal-complete-upto-1 = T.CliffT₂-minimal-complete-upto-1

  CliffCS₂-minimal-complete-upto-2 :
    (∀ {n} {w v : CliffCS.Circuit n} → n ≤ 3 →
       CliffCS-Sem.⟦ w ⟧ CliffCS-Sem.≈ CliffCS-Sem.⟦ v ⟧ → n CliffCS.⊢ w ≈ v) ×
    (∀ {n} {w v : CliffCS.Circuit n} (ρ : CliffCS._SRel,_===_ n w v) →
       n ≤ 2 → ¬ T.CliffCS-M.Complete-without ρ n)
  CliffCS₂-minimal-complete-upto-2 = T.CliffCS₂-minimal-complete-upto-2

  CNOTdihe₂-minimal-complete :
    (∀ {n} {w v : CNOTdihe.Circuit n} →
       CNOTdihe-Sem.⟦ w ⟧ CNOTdihe-Sem.≈ CNOTdihe-Sem.⟦ v ⟧ → n CNOTdihe.⊢ w ≈ v) ×
    (∀ {n} {w v : CNOTdihe.Circuit n} (ρ : CNOTdihe._SRel,_===_ n w v) →
       ¬ T.CNOTdihe-M.Complete-without ρ n)
  CNOTdihe₂-minimal-complete = T.CNOTdihe₂-minimal-complete

  CliffCS₂-clifford-complete : ∀ {n} {w v : Cliff.Circuit n} →
    Cliff-Sem.⟦ w ⟧ Cliff-Sem.≈ Cliff-Sem.⟦ v ⟧ →
    n CliffCS.⊢ Cliff→CliffCS w ≈ Cliff→CliffCS v
  CliffCS₂-clifford-complete {w = w} {v} = T.CliffCS₂-clifford-complete {w = w} {v}
