------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ as a PROP: the swap, with no relation of its own
--
-- Examples.Groups.Symmetric presents Sₙ in Circuit.Base's PRO, with two
-- relators of its own: the transposition σ is an involution (order) and
-- satisfies the braid relation (yang-baxter).  In Circuit.Prop's PROP
-- the transposition is the designated swap, and both are structure, not
-- relators: σ-inv is order, and σ-nat₂ at the swap itself is
-- yang-baxter.  What is left of the relation is nothing, so Sₙ is
-- presented by the free PROP on no generators — the circuit form of
-- Lafont's Theorem 1 ("Towards an algebraic theory of Boolean
-- circuits", J. Pure Appl. Algebra 184, 2003, §2.1).
--
-- The gates are Symmetric's, so the two developments have the same
-- circuits, word for word: Iso shows that their congruences coincide,
-- and Presentation carries Symmetric's theorems across.  Symmetric
-- itself is unchanged, as the PRO it is.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric-Prop.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Presentation.Construct.Base using (EmptyRel)
open import Presentation.GroupLike using (Grouplike)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)

import Circuit.Prop

open import Examples.Groups.Symmetric.Syntactics public
  using (Gate ; σ-gate ; σ-gen)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Syntactic framework: the PROP with the transposition as its swap

private module SC = Circuit.Prop Gate σ-gate

open SC public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; gate₃ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; _↓ᵏ_ ; _↧ᵏ_
        ; σ ; σ[_] ; σ⁻[_]
        ; _Sym,_===_ ; σ-inv ; σ-nat₁ ; σ-nat₂ ; σ-nat₃ )

------------------------------------------------------------------------
-- The relation: no relator of its own

infix 4 _SRel,_===_
_SRel,_===_ : (n : ℕ) → WRel (Gen n)
_SRel,_===_ n = EmptyRel

------------------------------------------------------------------------
-- The full relation: the swap rules (Circuit.Prop) and the structural
-- rules (Circuit.Base)
--
-- A swap rule s is srel (σrel s); sym-rule s as an equation.

private module LP = SC.Lift-To-Prop _SRel,_===_

open LP public
  using ( _Prop,_===_ ; σrel ; sym-rule ; srel
        ; cong↑ ; comm₁ ; comm₂ ; comm₃ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₂-w↑↑ ; _VRel,_===_ ; _⊢_≈_
        ; nat₁ ; nat₂ ; nat₃ ; nat₁⁻ ; nat₂⁻ ; nat₃⁻ )

-- Symmetric's two relators, as Circuit.Prop's laws at the swap.
order : (₂₊ n) ⊢ σ • σ ≈ ε
order = LP.σ-invol

yang-baxter : (₃₊ n) ⊢ σ • σ ↑ • σ ≈ σ ↑ • σ • σ ↑
yang-baxter = LP.yang-baxter

------------------------------------------------------------------------
-- Grouplike (the swap is its own inverse)

grouplike : Grouplike (_VRel,_===_ n)
grouplike {₂₊ k} (gate₂ σ-gate) = σ , order
grouplike {₁₊ n} (g ↥) with grouplike {n} g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
