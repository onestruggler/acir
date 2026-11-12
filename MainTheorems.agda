------------------------------------------------------------------------
-- Presentations of groups
--
-- Index of the paper formalizations: the main theorem of each paper
--
-- One section per source, in the order of the corpus table of the
-- OOPSLA draft (oopsla/sections/corpus.tex): groups of two-level
-- matrices, then circuits, then minimality.  Each section re-states the
-- paper's final result with its full type and proves it by reference
-- to the MainTheorem module of the development, named in the banner,
-- which it imports once: that module defines everything the statement
-- mentions and points to the modules that prove it, so this file is
-- also a reading guide.  A presentation (_IsPresentationOf_) says that
-- the relations present the whole group; a sub-presentation
-- (_IsSubPresentationOf_) that they present the subgroup the
-- generators generate, which for circuits is the group the paper is
-- about.  The intermediate results of each development — normal forms,
-- auxiliary equations, the layers of the qudit Clifford chain — are in
-- its own folder and its README; nothing here rests on a postulate.
--
-- The statements share one format.  The relations at dimension or
-- width n are n MRel,_===_ for words over two-level matrices (Word n)
-- and n CRel,_===_ for circuits (Circuit n), and a presentation is
--
--   ∀ n → (n MRel,_===_) IsPresentationOf (G n),
--   ∀ n → (n CRel,_===_) IsSubPresentationOf (G (2 ^ n)), …
--
-- Each of the fifteen sources before the minimality section also gets
-- its completeness and soundness theorems, for the semantics ⟦_⟧ its
-- presentation interprets the words in, in the form
--
--   complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
--   sound    : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
--
-- where ⊢ w ≈ v is equality by the relations (Presentation.Embedding
-- reads both off a presentation).  The groups of the Clifford+T family
-- — over ℤ[½], ℤ[½, i], ℤ[1/√2] and ℤ[1/√2, i] — are all read in one
-- semantics, Uₙ(𝔻[ω]), the unitary n × n matrices over 𝔻[ω] =
-- ℤ[1/√2, i] compared by their entries (_≈ᵁ_, Clifford+T-2qubit-
-- TwoLevel.Unitary): a group over a subring is carried there by the
-- inclusion of the entries (EucDomain's Quantum.Synthesis.Ring.
-- Properties.Embedding and Quantum.Synthesis.Matrix.Map, assembled in
-- Clifford+T-2qubit-TwoLevel.Subring), in a DOmega module of its
-- development.  The qudit, phase-affine and qutrit sources keep their
-- own semantics (_≈ᶜ_, _≈ᴬ_, _≈ˢ_).  The minimality section states,
-- for each fragment's rule set on n wires (n ⊢_===_),
--
--   minimal-complete : ∀ {n} → (n ⊢_===_) IsMinimal × (n ⊢_===_) IsComplete
--
-- with the paper's bounds on n where it has them.
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
open import Data.Nat using (ℕ ; 2+ ; _≤_ ; _^_)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_×_ ; _,_ ; ∃)
open import Function.Bundles using (Inverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

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
-- Home: Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTheorem.  The
-- two-level generators ω_[a], H_[a,b], X_[a,b] and Greylyn's relations
-- present Uₙ(ℤ[1/√2, i]) for n ≤ 4, by the main lemma of the exact
-- synthesis algorithm, as the thesis does.

module Greylyn where

  open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTheorem as M
    using (Word ; _MRel,_===_ ; U ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_)

  presentation : ∀ n → n ≤ 4 → (n MRel,_===_) IsPresentationOf (U n)
  presentation = M.presentation

  complete : ∀ {n} → n ≤ 4 → {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Bian and Selinger (2021): Uₙ(ℤ[½, i])
--
-- Home: Examples.Groups.Clifford+CS-TwoLevel.MainTheorem.  The
-- two-level generators and the relations of their Figure 1 present
-- Uₙ(ℤ[½, i]) in every dimension.  Uₙ(ℤ[½, i]) is a subgroup of
-- Uₙ(𝔻[ω]), where the matrices are compared.

module Bian-Selinger-Un where

  open import Examples.Groups.Clifford+CS-TwoLevel.MainTheorem as M
    using (Word ; _MRel,_===_ ; U ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_)

  presentation : ∀ n → (n MRel,_===_) IsPresentationOf (U n)
  presentation = M.presentation

  complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Li, Ross and Selinger (2021): Oₙ(ℤ[½]) and Lₙ
--
-- Home: Examples.Groups.CCX+HH-TwoLevel.MainTheorem.  (−1)_[a],
-- X_[a,b], K_[a,b,c,d] and Table 1 present Oₙ(ℤ[½]) in every dimension
-- (Theorem 4.10), and with I ⊗ H and Table 2 the scaled dyadic
-- orthogonal matrices Lₙ, for n = 2(k + 1) (Theorem 5.7), here indexed
-- by k.  Both are subgroups of Uₙ(𝔻[ω]).

module Li-Ross-Selinger where

  open import Examples.Groups.CCX+HH-TwoLevel.MainTheorem as M
    using ( Word ; _MRel,_===_ ; O ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_
          ; Wordᴸ ; _MRelᴸ,_===_ ; L ; ⟦_⟧ᴸ_ ; _⊢ᴸ_≈_ )

  presentation : ∀ n → (n MRel,_===_) IsPresentationOf (O n)
  presentation = M.presentation

  complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

  -- The same for Lₙ, n = 2(k + 1), with k explicit: a word does not
  -- determine it.
  presentationᴸ : ∀ k → (k MRelᴸ,_===_) IsPresentationOf (L k)
  presentationᴸ = M.presentationᴸ

  completeᴸ : ∀ k {w v : Wordᴸ k} → ⟦ k ⟧ᴸ w ≈ᵁ ⟦ k ⟧ᴸ v → k ⊢ᴸ w ≈ v
  completeᴸ = M.completeᴸ

  soundᴸ : ∀ k {w v : Wordᴸ k} → k ⊢ᴸ w ≈ v → ⟦ k ⟧ᴸ w ≈ᵁ ⟦ k ⟧ᴸ v
  soundᴸ = M.soundᴸ

------------------------------------------------------------------------
-- Fang, Heunen and Kaarsgaard (2026), Hadamard-Π: Oₙ(ℤ[1/√2])
--
-- Home: Examples.Groups.Real-Clifford+CH-TwoLevel.MainTheorem.  Z_[a],
-- X_[a,b], H_[a,b] and the relations (a1)–(d4) of Figure 6 present
-- Oₙ(ℤ[1/√2]) in every dimension.  The paper's proof does not cover one
-- case of its Main Lemma (its Lemmas A.16 and A.17 are false); the
-- development proves the theorem from that case, Hard, and the case
-- itself after Clément's thesis (below).

module Hadamard-Pi where

  open import Examples.Groups.Real-Clifford+CH-TwoLevel.MainTheorem as M
    using (Word ; _MRel,_===_ ; O ; Hard ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_)

  -- The paper's proof, given the case it misses ...
  presentation-given : ∀ n → Hard {n} → (n MRel,_===_) IsPresentationOf (O n)
  presentation-given = M.presentation-given

  -- ... and the theorem.
  presentation : ∀ n → (n MRel,_===_) IsPresentationOf (O n)
  presentation = M.presentation

  -- Completeness by the paper's proof, given the case it misses ...
  complete-given : ∀ {n} → Hard {n} → {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete-given = M.complete-given

  -- ... and the theorem.
  complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Clément (2019, thesis): Oₙ(ℤ[1/√2]) by relations (1)–(21)
--
-- Home: Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.
-- MainTheorem.  Clément's own proof, over his version of the synthesis
-- algorithm: his relations (_MRelᶜ,_===_), and Figure 6, present
-- Oₙ(ℤ[1/√2]) in every dimension.

module Clement-Thesis where

  open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.MainTheorem as M
    using (Word ; _MRelᶜ,_===_ ; _MRel,_===_ ; O ; ⟦_⟧ ; _≈ᵁ_ ; ⊢ᶜ_≈_ ; ⊢_≈_)

  presentationᶜ : ∀ n → (n MRelᶜ,_===_) IsPresentationOf (O n)
  presentationᶜ = M.presentationᶜ

  presentation : ∀ n → (n MRel,_===_) IsPresentationOf (O n)
  presentation = M.presentation

  completeᶜ : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ᶜ w ≈ v
  completeᶜ = M.completeᶜ

  soundᶜ : ∀ {n} {w v : Word n} → ⊢ᶜ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  soundᶜ = M.soundᶜ

  complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Circuits
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Selinger (2015): n-qubit Clifford circuits
--
-- Home: Examples.Groups.Qubit-Clifford.MainTheorem.  The gates ω, H, S,
-- CZ and the relations C1–C15 of Figure 8 present the group the
-- circuits on n wires generate in U_{2ⁿ}(𝔻[ω]), at every width.

module Selinger-Clifford where

  open import Examples.Groups.Qubit-Clifford.MainTheorem as M
    using (Circuit ; _CRel,_===_ ; U ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (2 ^ n)
  presentation = M.presentation

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Bian et al. (2026): qudit Clifford circuits, odd prime p
--
-- Home: Examples.Groups.Clifford+MinusOne.Qupit.MainTheorem, and the
-- sources of its Figure1.Presentation (the symplectic normal form, the
-- projective chain of ProjectiveClifford.Qupit, Qupit-Clifford).  The
-- gates −ω, H, S, CZ and the rules C0–C15 of Figure 1 present the qudit
-- Clifford group at every width: the paper's Theorem 4.10, against the
-- algebraic model, the central extension of Pauli ⋊ Sp(2n, ℤ/pℤ) by
-- ⟨ω⟩ (the Weyl cocycle) times ⟨−1⟩.  The rules name a primitive root g
-- of ℤ/pℤ.

module Qudit-Clifford
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (2+ p-2))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x Eq.≡ g ^′ toℕ k)
  where

  open import Examples.Groups.Clifford+MinusOne.Qupit.MainTheorem p-3 p-prime g* g-gen as M
    using (Circuit ; _CRel,_===_ ; Clifford± ; ⟦_⟧ ; _≈ᶜ_ ; ⊢_≈_)

  presentation : ∀ n → (n CRel,_===_) IsPresentationOf (Clifford± n)
  presentation = M.presentation

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᶜ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᶜ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Makary, Ross and Selinger (2021): real stabilizer circuits
--
-- Home: Examples.Groups.Real-Clifford.MainTheorem.  The gates −1, H, Z,
-- CZ and the relations R1–R16 of Figure 1 present the group the
-- circuits generate, at every width, in U_{2ⁿ}(𝔻[ω]) and in
-- O_{2ⁿ}(ℤ[1/√2]).

module Makary-Ross-Selinger where

  open import Examples.Groups.Real-Clifford.MainTheorem as M
    using (Circuit ; _CRel,_===_ ; U ; O ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (2 ^ n)
  presentation = M.presentation

  presentationᴼ : ∀ n → (n CRel,_===_) IsSubPresentationOf O (2 ^ n)
  presentationᴼ = M.presentationᴼ

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Amy, Chen and Ross (2018): CNOT-dihedral circuits
--
-- Home: Examples.Groups.CNOT+Dihedral.MainTheorem.  The gates ω, X, T,
-- CNOT and the relations R₁–R₁₃ of Figure 1, with the swap rules,
-- present the group the circuits generate in U_{2ⁿ}(𝔻[ω]), at every
-- width.

module Amy-Chen-Ross where

  open import Examples.Groups.CNOT+Dihedral.MainTheorem as M
    using (Circuit ; _CRel,_===_ ; U ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (2 ^ n)
  presentation = M.presentation

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Blake (2026): phase-affine circuits in prime dimension p
--
-- Home: Examples.Groups.Qupit-Phase-Affine.MainTheorem.  The four
-- levels — affine circuits, then phases, then S (p odd), then T
-- (p > 3) — each present the group their circuits generate in U_{pⁿ},
-- over any commutative ring with an involution and an injective
-- character of 𝔽_p: Theorem 1 and its three extensions.

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

  open import Examples.Groups.Qupit-Phase-Affine.MainTheorem
    p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective as M
    using (p ; U ; _≈ᴬ_)

  -- Affine circuits: Theorem 1.
  module Affine where

    open M.Affine using (Circuit ; _CRel,_===_ ; ⟦_⟧ ; ⊢_≈_)

    presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
    presentation = M.Affine.presentation

    complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
    complete = M.Affine.complete

    sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
    sound = M.Affine.sound

  -- With phases.
  module Linear-Phase where

    open M.Linear-Phase using (Circuit ; _CRel,_===_ ; ⟦_⟧ ; ⊢_≈_)

    presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
    presentation = M.Linear-Phase.presentation

    complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
    complete = M.Linear-Phase.complete

    sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
    sound = M.Linear-Phase.sound

  -- With S, for p odd.
  module Quadratic (odd : 1 ≤ p-2) where

    open M.Quadratic odd using (Circuit ; _CRel,_===_ ; ⟦_⟧ ; ⊢_≈_)

    presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
    presentation = M.Quadratic.presentation odd

    complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
    complete = M.Quadratic.complete odd

    sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
    sound = M.Quadratic.sound odd

  -- With T, for p > 3.
  module Cubic (gt3 : 2 ≤ p-2) where

    open M.Cubic gt3 using (Circuit ; _CRel,_===_ ; ⟦_⟧ ; ⊢_≈_)

    presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
    presentation = M.Cubic.presentation gt3

    complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
    complete = M.Cubic.complete gt3

    sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
    sound = M.Cubic.sound gt3

------------------------------------------------------------------------
-- Bian and Selinger (2023): two-qubit Clifford+T circuits
--
-- Home: Examples.Groups.Clifford+T-2qubit.MainTheorem.  The relations of
-- Figure 1 present the two-qubit Clifford+T group in U₄(ℤ[1/√2, i]), as
-- circuits over Circuit.Base on two wires and over the paper's
-- alphabet (ᴾ).

module Bian-Selinger-Clifford+T where

  open import Examples.Groups.Clifford+T-2qubit.MainTheorem as M
    using ( Circuit ; _CRel,_===_ ; U ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_
          ; Wordᴾ ; _===ᴾ_ ; ⟦_⟧ᴾ ; ⊢ᴾ_≈_ )

  presentation : (2 CRel,_===_) IsSubPresentationOf U 4
  presentation = M.presentation

  complete : ∀ {w v : Circuit 2} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {w v : Circuit 2} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

  -- The paper's alphabet.
  presentationᴾ : _===ᴾ_ IsSubPresentationOf U 4
  presentationᴾ = M.presentationᴾ

  completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
  completeᴾ = M.completeᴾ

  soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
  soundᴾ = M.soundᴾ

------------------------------------------------------------------------
-- Bian and Selinger (2023): three-qubit Clifford+CS circuits
--
-- Home: Examples.Groups.Clifford+CS-3qubit.MainTheorem.  The relations
-- of Figure 2 present the three-qubit Clifford+CS group in U₈(ℤ[½, i]),
-- as circuits over Circuit.Base on three wires and over the paper's
-- alphabet (ᴾ).  U₈(ℤ[½, i]) is a subgroup of U₈(𝔻[ω]).

module Bian-Selinger-Clifford+CS where

  open import Examples.Groups.Clifford+CS-3qubit.MainTheorem as M
    using ( Circuit ; _CRel,_===_ ; U ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_
          ; Wordᴾ ; _===ᴾ_ ; ⟦_⟧ᴾ ; ⊢ᴾ_≈_ )

  presentation : (3 CRel,_===_) IsSubPresentationOf U 8
  presentation = M.presentation

  complete : ∀ {w v : Circuit 3} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {w v : Circuit 3} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

  -- The paper's alphabet.
  presentationᴾ : _===ᴾ_ IsSubPresentationOf U 8
  presentationᴾ = M.presentationᴾ

  completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
  completeᴾ = M.completeᴾ

  soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
  soundᴾ = M.soundᴾ

------------------------------------------------------------------------
-- Clément (2026): real Clifford+CH circuits
--
-- Home: Examples.Groups.Real-Clifford+CH.MainTheorem.  The gates H, Z,
-- CZ, CH and the relations of Figure 4 present the group the circuits
-- on n wires generate in O_{2ⁿ}(ℤ[1/√2]), at every width: Theorem 8.9,
-- with Theorem 4.4, which the paper imports from Hadamard-Π, proved
-- from Clément's thesis.  O_{2ⁿ}(ℤ[1/√2]) is a subgroup of
-- U_{2ⁿ}(𝔻[ω]).

module Clement-Real-Clifford+CH where

  open import Examples.Groups.Real-Clifford+CH.MainTheorem as M
    using (Circuit ; _CRel,_===_ ; O ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf O (2 ^ n)
  presentation = M.presentation

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Amy, Ross and Wesley (2024): three-qubit Toffoli-Hadamard circuits
--
-- Homes: Examples.Groups.CCX+H-3qubit-Tietze.MainTheorem and
-- Examples.Groups.CCX+H-3qubit-RS.MainTheorem.  The relations of
-- Figures 4, 7 and 8, corrected and with the definition of K that
-- Section 5.5 uses but the figures omit, present L₈, the group of
-- 3-qubit Toffoli-Hadamard operators (scaled dyadic orthogonal 8 × 8
-- matrices), as circuits over Circuit.Base on three wires and over the
-- paper's alphabet (ᴾ).  L₈ is a subgroup of U₈(𝔻[ω]).
--
-- The theorem has four formalizations, two in Agda, restated below in
-- one format, and two in Lean.  Each decodes Li-Ross-Selinger's
-- generators into circuits and concludes from their presentations of
-- O₈(𝔻) and L₈; they differ in where the circuit identities come from.
--
-- * CCX+H-3qubit-Tietze (module Amy-Ross-Wesley) replays the authors'
--   own derivations, from their TIETZE2 files (CircuitLemmas).
-- * CCX+H-3qubit-RS (module Amy-Ross-Wesley-RS) derives them by a
--   breadth-first search over Figure 4 (gen/); its decoding is Figure
--   7's letters conjugated by Coxeter words (Decode).
-- * Lean/QCert/ToffoliHadamard (theorem_5_2 and theorem_6_3 in
--   Theorem.lean) was written from the paper, over a macro alphabet,
--   with a kernel-checked Knuth-Bendix system for S₈.
-- * Lean/QCert/ToffoliHadamardRS (theorem_5_2, theorem_6_3,
--   circuits_5_2, circuits_6_3 and r_K_independent in Theorem.lean) is
--   a translation of CCX+H-3qubit-RS, module for module, with the same
--   derivations; its S₈ facts are proved by a normal form of its own
--   (CoxeterFrames).

module Amy-Ross-Wesley where

  open import Examples.Groups.CCX+H-3qubit-Tietze.MainTheorem as M
    using ( Circuit ; _CRel,_===_ ; ToffoliHadamard ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_
          ; Wordᴾ ; _===ᴾ_ ; ⟦_⟧ᴾ ; ⊢ᴾ_≈_ )

  presentation : (3 CRel,_===_) IsPresentationOf ToffoliHadamard
  presentation = M.presentation

  complete : ∀ {w v : Circuit 3} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {w v : Circuit 3} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

  -- The paper's alphabet.
  presentationᴾ : _===ᴾ_ IsPresentationOf ToffoliHadamard
  presentationᴾ = M.presentationᴾ

  completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
  completeᴾ = M.completeᴾ

  soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
  soundᴾ = M.soundᴾ

-- The same theorem, by CCX+H-3qubit-RS.

module Amy-Ross-Wesley-RS where

  open import Examples.Groups.CCX+H-3qubit-RS.MainTheorem as M
    using ( Circuit ; _CRel,_===_ ; ToffoliHadamard ; ⟦_⟧ ; _≈ᵁ_ ; ⊢_≈_
          ; Wordᴾ ; _===ᴾ_ ; ⟦_⟧ᴾ ; ⊢ᴾ_≈_ )

  presentation : (3 CRel,_===_) IsPresentationOf ToffoliHadamard
  presentation = M.presentation

  complete : ∀ {w v : Circuit 3} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {w v : Circuit 3} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
  sound = M.sound

  -- The paper's alphabet.
  presentationᴾ : _===ᴾ_ IsPresentationOf ToffoliHadamard
  presentationᴾ = M.presentationᴾ

  completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
  completeᴾ = M.completeᴾ

  soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
  soundᴾ = M.soundᴾ

------------------------------------------------------------------------
-- Li, Mosca, Ross, van de Wetering and Zhao (2025): qutrit Clifford
-- circuits
--
-- Home: Examples.Groups.Qutrit-Clifford.MainTheorem.  The gates −ω, H,
-- S, CZ and the rules C1–C18 of Figure 1 present the n-qutrit Clifford
-- group — the values the circuits denote, exact scaled matrices over
-- ℤ[ζ₁₂] — at every width, and that group has order 6 · ∏ₖ₌₁ⁿ
-- 3 (9ᵏ − 1) 9ᵏ.

module Li-Mosca-Ross-vandeWetering-Zhao where

  open import Examples.Groups.Qutrit-Clifford.MainTheorem as M
    using (Circuit ; _CRel,_===_ ; Clifford ; order ; ⟦_⟧ ; _≈ˢ_ ; ⊢_≈_)

  presentation : ∀ n → (n CRel,_===_) IsPresentationOf Clifford n
  presentation = M.presentation

  clifford-order : ∀ n → Inverse (Group.setoid (Clifford n)) (Eq.setoid (Fin (order n)))
  clifford-order = M.clifford-order

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ˢ ⟦ v ⟧ → ⊢ w ≈ v
  complete = M.complete

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
  sound = M.sound

------------------------------------------------------------------------
-- Minimality
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Blake (2026): simpler presentations for six fragments
--
-- Homes: Examples.Independence.<fragment>.MainTheorem.  For each
-- fragment — qubit Clifford (Cliff₂), real Clifford (RCliff₂), qutrit
-- Clifford (Cliff₃), Clifford+T (CliffT₂), Clifford+CS (CliffCS₂),
-- CNOT-dihedral (CNOTdihe₂) — the rule set on n wires (n ⊢_===_) is
-- complete (Theorem 22, by transfer from the presentations above, in
-- the paper's ranges of widths) and minimal: without any one of its
-- axioms of arity n it is not complete on n wires (Theorem 37, by
-- separating models, and soundness; Examples.Independence.
-- MinimalComplete), so it is a minimal complete presentation of the
-- matrix semantics.

module Blake-Minimality where

  -- Qubit Clifford: minimal and complete at every width.
  module Cliff₂ where

    open import Examples.Independence.Clifford.MainTheorem as M
      using (_⊢_===_ ; _IsMinimal ; _IsComplete)

    minimal-complete : ∀ {n} → (n ⊢_===_) IsMinimal × (n ⊢_===_) IsComplete
    minimal-complete = M.minimal-complete

  -- Real Clifford: minimal and complete at every width.
  module RCliff₂ where

    open import Examples.Independence.Real-Clifford.MainTheorem as M
      using (_⊢_===_ ; _IsMinimal ; _IsComplete)

    minimal-complete : ∀ {n} → (n ⊢_===_) IsMinimal × (n ⊢_===_) IsComplete
    minimal-complete = M.minimal-complete

  -- Qutrit Clifford: minimal on at most two wires, complete at every
  -- width.
  module Cliff₃ where

    open import Examples.Independence.Qutrit-Clifford.MainTheorem as M
      using (_⊢_===_ ; _IsMinimal ; _IsComplete)

    minimal-complete : ∀ {n} → (n ≤ 2 → (n ⊢_===_) IsMinimal) × (n ⊢_===_) IsComplete
    minimal-complete = M.minimal-complete

  -- Clifford+T: minimal on at most one wire, complete on at most two.
  module CliffT₂ where

    open import Examples.Independence.Clifford+T.MainTheorem as M
      using (_⊢_===_ ; _IsMinimal ; _IsComplete)

    minimal-complete : ∀ {n} → (n ≤ 1 → (n ⊢_===_) IsMinimal) × (n ≤ 2 → (n ⊢_===_) IsComplete)
    minimal-complete = M.minimal-complete

  -- Clifford+CS: minimal on at most two wires, complete on at most
  -- three.
  module CliffCS₂ where

    open import Examples.Independence.Clifford+CS.MainTheorem as M
      using (_⊢_===_ ; _IsMinimal ; _IsComplete)

    minimal-complete : ∀ {n} → (n ≤ 2 → (n ⊢_===_) IsMinimal) × (n ≤ 3 → (n ⊢_===_) IsComplete)
    minimal-complete = M.minimal-complete

  -- CNOT-dihedral: minimal and complete at every width.
  module CNOTdihe₂ where

    open import Examples.Independence.CNOT-Dihedral.MainTheorem as M
      using (_⊢_===_ ; _IsMinimal ; _IsComplete)

    minimal-complete : ∀ {n} → (n ⊢_===_) IsMinimal × (n ⊢_===_) IsComplete
    minimal-complete = M.minimal-complete
