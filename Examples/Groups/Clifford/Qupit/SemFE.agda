------------------------------------------------------------------------
-- Presentations of groups
--
-- The qupit factor set, from the Weyl cocycle.
--
-- Clifford.Qupit.SemGeneratorData reduces the `GeneratorData` record
-- that the scalar layer's cocycle is built from to a FACTOR SET for the
-- quotient,
--
--     FactorSet ℤ/pℤ (H n) trivial  →  GeneratorData n,
--
-- and its header records that the factor set itself does not exist —
-- naming three things a construction of it would need: a normalised
-- section of the quotient, a scalar-kernel theorem, and ω-faithfulness.
-- That is the shape a factor set built as the DEFECT OF A LIFTING has
-- to take, and it is how the qubit development builds its (Qubit.SemFE).
--
-- This file builds one a different way, and needs none of the three.
-- Clifford.Qupit.Semantics already proves `weyl`: the Weyl cocycle
--
--     cocy (P , S) (Q , _) = ½ · sform P (ap S Q)
--
-- on Pauli n ⋊ Sp(2n, ℤ/pℤ), with all four laws — normalisation on
-- either side, congruence, and the cocycle identity, the last of which
-- is symplectic invariance of sform.  A cocycle on a group pulls back
-- along ANY homomorphism into it, and Paper-V0.Presentation is exactly
-- such a homomorphism out of the word group H n.  So
--
--     fa u v = cocy ⟦ u ⟧ ⟦ v ⟧
--
-- is a factor set on H n with nothing left to prove but the pullback.
-- No section is chosen, no scalar kernel is computed, and ω-faithfulness
-- is not needed at all — in this model ω is faithful by construction,
-- the kernel being ℤ/pℤ itself.
--
-- The one thing that did have to be proved is that the two semidirect
-- products agree.  Paper-V0.Presentation lands in SemiDirect.
-- Presentation.Semidirect.Pauli⋊Sp, whose action is TRANSPORTED — a
-- symplectic element acts on a Pauli by conjugating representative words
-- and reading the result back — while Semantics' Pauli⋊Sp-group acts by
-- `ap`.  Both are SDP.group (+ₚ-group n) (Sp-group n) at their
-- respective actions, so they differ in nothing but that; `act≡ap` and
-- `∙-agrees`, proved in SemiDirect.Presentation (where the transported
-- action is in scope), close the gap, and `⟦⟧-∙` below is the pullback's
-- only non-formal step.
--
-- What this does NOT give.  A cocycle is not yet the RIGHT cocycle:
-- Presented-Extension.Realises — that the corrections it accumulates are
-- the ones `corr` records — is a separate statement, and the split
-- cocycle shows it does not come for free.  Proving it means checking,
-- for each of the sixteen Paper-V0 relations, that the ½·sform
-- accumulated along the two sides differs by exactly corr: zero for
-- fifteen of them and ω^((p²-1)/8) for order-SH.  That is the qupit
-- analogue of Selinger.ScalarKernel and is still open.  With this file,
-- it is the ONLY thing still open: Clifford.Qupit.Presentation's
-- presentation theorem now takes one hypothesis rather than two.
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

module Examples.Groups.Clifford.Qupit.SemFE
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (Word ; ε ; _•_)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

import ForStdlib.Algebra.Construct.FactorSetExtension as FSE
open FSE using (FactorSet)

-- The quotient's presentation, and the identification of the group it
-- presents with the one the Weyl cocycle lives on.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Presentation
  p-3 p-prime g* g-gen as PapPres
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  p-3 p-prime g* g-gen as SDPres

-- The syntax, the semantics, and the reduction to a factor set.
import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS
import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem
import Examples.Groups.Clifford.Qupit.SemGeneratorData
  p-3 p-prime g* g-gen as SGD

module PE = Sem.Presented-Extension g* g-gen

------------------------------------------------------------------------
-- The factor set, one width at a time

module Weyl (n : ℕ) where

  private
    -- The quotient, syntactically and structurally.
    module QB = PB (QS.CR._QRel,_===_ n)
    module C  = Group (Sem.Pauli⋊Sp-group n)
    module SD = SDPres.Semidirect n

    module PP   = _IsPresentationOf_ (PapPres.presentation n)
    module PIso = GroupMorphisms.IsGroupIsomorphism PP.iso

    ------------------------------------------------------------------
    -- Equality in Pauli ⋊ Sp is a pair
    --
    -- Both endpoints are taken EXPLICITLY, for the reason Semantics
    -- gives: the second component compares symplectic transformations
    -- through their ACTIONS, so unifying a `_≈_` goal eta-expands the
    -- Symplectic record and leaves every field but `ap` unsolved.

    C-refl : ∀ (x : C.Carrier) → C._≈_ x x
    C-refl x = Eq.refl , λ _ → Eq.refl

    C-sym : ∀ (x y : C.Carrier) → C._≈_ x y → C._≈_ y x
    C-sym x y (e₁ , e₂) = Eq.sym e₁ , λ q → Eq.sym (e₂ q)

  ----------------------------------------------------------------------
  -- The quotient's denotation, read in the structural model
  --
  -- Paper-V0's own interpretation, retyped: its target is the
  -- transported semidirect product, which has the same carrier and the
  -- same equality as Semantics' Pauli⋊Sp-group.

  ⟦_⟧ : Word (QS.Gen n) → C.Carrier
  ⟦_⟧ = PP.⟦_⟧

  ⟦⟧-cong : ∀ {u v} → QB._≈_ u v → C._≈_ ⟦ u ⟧ ⟦ v ⟧
  ⟦⟧-cong = PIso.⟦⟧-cong

  ⟦⟧-ε : C._≈_ ⟦ ε ⟧ C.ε
  ⟦⟧-ε = PIso.ε-homo

  -- The only step that is not formal: the multiplication Paper-V0's
  -- interpretation is a homomorphism for is the transported one, and
  -- `∙-agrees` says that is Semantics'.
  ⟦⟧-∙ : ∀ u v → C._≈_ ⟦ u • v ⟧ (⟦ u ⟧ C.∙ ⟦ v ⟧)
  ⟦⟧-∙ u v =
    Eq.subst (C._≈_ ⟦ u • v ⟧) (SD.∙-agrees ⟦ u ⟧ ⟦ v ⟧) (PIso.∙-homo u v)

  ----------------------------------------------------------------------
  -- The pullback of the Weyl cocycle
  --
  -- Each law is Semantics' corresponding law at the denotations, with
  -- the homomorphism laws above used to move ⟦_⟧ across a product.  The
  -- implicits of cocy-cong are written out throughout: _≈_ on Pauli ⋊ Sp
  -- computes, so unification never recovers them.

  fa : Word (QS.Gen n) → Word (QS.Gen n) → ℤ ₚ
  fa u v = Sem.cocy n ⟦ u ⟧ ⟦ v ⟧

  fa-cong : ∀ {u u' v v'} → QB._≈_ u u' → QB._≈_ v v' → fa u v ≡ fa u' v'
  fa-cong {u} {u'} {v} {v'} eu ev =
    Sem.cocy-cong n {⟦ u ⟧} {⟦ u' ⟧} {⟦ v ⟧} {⟦ v' ⟧} (⟦⟧-cong eu) (⟦⟧-cong ev)

  fa-εˡ : ∀ v → fa ε v ≡ ₀
  fa-εˡ v =
    Eq.trans (Sem.cocy-cong n {⟦ ε ⟧} {C.ε} {⟦ v ⟧} {⟦ v ⟧} ⟦⟧-ε (C-refl ⟦ v ⟧))
             (Sem.cocy-εˡ n ⟦ v ⟧)

  fa-εʳ : ∀ u → fa u ε ≡ ₀
  fa-εʳ u =
    Eq.trans (Sem.cocy-cong n {⟦ u ⟧} {⟦ u ⟧} {⟦ ε ⟧} {C.ε} (C-refl ⟦ u ⟧) ⟦⟧-ε)
             (Sem.cocy-εʳ n ⟦ u ⟧)

  fa-cocycle : ∀ u v w → (fa u v + fa (u • v) w) ≡ (fa v w + fa u (v • w))
  fa-cocycle u v w =
    Eq.trans (Eq.cong (fa u v +_) left)
      (Eq.trans (Sem.cocy-assoc n ⟦ u ⟧ ⟦ v ⟧ ⟦ w ⟧)
                (Eq.cong (fa v w +_) right))
    where
    left : fa (u • v) w ≡ Sem.cocy n (⟦ u ⟧ C.∙ ⟦ v ⟧) ⟦ w ⟧
    left = Sem.cocy-cong n {⟦ u • v ⟧} {⟦ u ⟧ C.∙ ⟦ v ⟧} {⟦ w ⟧} {⟦ w ⟧}
                           (⟦⟧-∙ u v) (C-refl ⟦ w ⟧)
    right : Sem.cocy n ⟦ u ⟧ (⟦ v ⟧ C.∙ ⟦ w ⟧) ≡ fa u (v • w)
    right = Sem.cocy-cong n {⟦ u ⟧} {⟦ u ⟧} {⟦ v ⟧ C.∙ ⟦ w ⟧} {⟦ v • w ⟧}
                            (C-refl ⟦ u ⟧)
                            (C-sym ⟦ v • w ⟧ (⟦ v ⟧ C.∙ ⟦ w ⟧) (⟦⟧-∙ v w))

  ----------------------------------------------------------------------
  -- ... is a factor set

  factorSet : FactorSet SGD.Scalars (PE.H n) (SGD.Trivial n)
  factorSet = record
    { f                   = fa
    ; isNormalisedCocycle = record
      { f-cong  = fa-cong
      ; f-εˡ    = fa-εˡ
      ; f-εʳ    = fa-εʳ
      ; cocycle = fa-cocycle
      }
    }

  ----------------------------------------------------------------------
  -- ... hence the generator data, unconditionally
  --
  -- SemGeneratorData does the rest: the reduction is CocycleGen's
  -- From-FactorSet and the transport ℤ/pℤ → words is Cyclic.Scalars.

  generator-data : PE.GeneratorData n
  generator-data = SGD.From-FactorSet.generator-data n factorSet

------------------------------------------------------------------------
-- The theorem
--
-- The generator data the scalar layer's cocycle is built from exists at
-- every width, with no hypothesis.

generator-data : ∀ (n : ℕ) → PE.GeneratorData n
generator-data = Weyl.generator-data
