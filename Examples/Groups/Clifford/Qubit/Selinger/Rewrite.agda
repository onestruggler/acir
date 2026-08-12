------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6), one qubit.
--
-- §6 converts a circuit to normal form by rewriting: append the normal
-- form of the identity (6.4) to get a "dirty normal form" (Definition
-- 6.1) -- a normal form with extra H, S, X and controlled-Z gates
-- interspersed -- and then push every dirty gate rightwards into the
-- clean boxes using the rules of Figures 3-7 until none is left.
--
-- Following Symplectic rather than the paper, this is built as an
-- ACTION on normal-form data rather than as a rewrite relation: for
-- each generator g a function taking the datum of N to the datum of
-- g·N.  The paper's rules are exactly the clauses of that function, and
-- its termination argument (§6, the lexicographic measure on dirty
-- gates) becomes the structural recursion that computes it.  What the
-- rewrite relation gives extra -- that the rules are confluent -- is
-- not needed, since the action is a function.
--
-- This module is the one-qubit layer, the base of the tower.  At one
-- qubit a normal form is Aᵢ·C_k·E_h·ωᵖ, and the only generators are H,
-- S and the scalar; the dirt that can reach each box is correspondingly
-- limited, which is what DirtA, DirtC and DirtE record.
--
-- Direction.  The rules read "dirty gate BEFORE clean box", so this is
-- a LEFT action: act d nf is the normal form of [d]·[nf].  That is the
-- direction Proposition 6.3 uses, appending the identity's normal form
-- to the right of the given circuit.
--
-- The rules are transcribed from the arXiv source of Figures 3-7, whose
-- macros are named for the pair they treat: commHA, commSA (into A),
-- commXC, commSC (into C), altSE (into E).  Each carries a comment
-- giving the phase and the word, e.g.
--
--   % (0,[Sx 0,A 3 0])  =  % (1,[A 2 0,Sx 0,Sx 0,Sx 0])
--
-- i.e. S·A₃ = ω·A₂·S³.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Rewrite
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤ ; tt)

open import ForStdlib.Data.Fin.Mod using (ℤ ; _+_ ; ₀ ; ₁ ; ₂)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (NF)

open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; _↥
        ; ω-gate ; H-gate ; S-gate )

------------------------------------------------------------------------
-- The dirty gates
--
-- Definition 6.1 allows H, S, X and controlled-Z as dirt, but which
-- ones can reach which box is fixed by the wire labels: at one qubit an
-- A box can be met by H or S, a C box by X or S, and an E box by S
-- alone.  Giving each stage its own type makes the push functions total
-- and records that discipline in the types.

data DirtA : Set where
  dH dS : DirtA

data DirtC : Set where
  dX dS : DirtC

data DirtE : Set where
  dS : DirtE

------------------------------------------------------------------------
-- Pushing one dirty gate into one clean box
--
-- Each clause is one equation of Figures 3-7, read left to right: the
-- result is a phase, the new box, and the dirt that emerges on its
-- right.

-- Figure 3: commHA and commSA.
pushA : DirtA → ABox → ℤ 8 × ABox × List DirtC
pushA dH a₁ = ₀ , a₂ , []
pushA dH a₂ = ₀ , a₁ , []
pushA dH a₃ = ₁ , a₃ , dX ∷ dS ∷ dS ∷ dS ∷ []
pushA dS a₁ = ₀ , a₁ , dS ∷ []
pushA dS a₂ = ₁ , a₃ , dX ∷ dS ∷ dS ∷ dS ∷ []
pushA dS a₃ = ₁ , a₂ , dS ∷ dS ∷ dS ∷ []

-- commXC and commSC.  Only S survives a C box, which is why an E box
-- never meets an X.
pushC : DirtC → CBox → ℤ 8 × CBox × List DirtE
pushC dX c₁ = ₀ , c₂ , []
pushC dX c₂ = ₀ , c₁ , []
pushC dS c₁ = ₀ , c₁ , dS ∷ []
pushC dS c₂ = ₂ , c₂ , dS ∷ dS ∷ dS ∷ []

-- altSE: S steps the phase box on by one, and nothing comes out.
pushE : DirtE → EBox → ℤ 8 × EBox
pushE dS e₁ = ₀ , e₂
pushE dS e₂ = ₀ , e₃
pushE dS e₃ = ₀ , e₄
pushE dS e₄ = ₀ , e₁

------------------------------------------------------------------------
-- Pushing a whole word of dirt
--
-- In d₁·d₂·Box the gate meeting the box is d₂, so a list is consumed
-- from the right.  The dirt that emerges keeps that order: pushing d₂
-- leaves o₂ to the right of the box, and then d₁ leaves o₁ to the left
-- of o₂.

pushC* : List DirtC → CBox → ℤ 8 × CBox × List DirtE
pushC* []       c = ₀ , c , []
pushC* (d ∷ ds) c with pushC* ds c
... | k₂ , c′ , o₂ with pushC d c′
...   | k₁ , c″ , o₁ = k₁ + k₂ , c″ , o₁ ++ o₂

pushE* : List DirtE → EBox → ℤ 8 × EBox
pushE* []       e = ₀ , e
pushE* (d ∷ ds) e with pushE* ds e
... | k₂ , e′ with pushE d e′
...   | k₁ , e″ = k₁ + k₂ , e″

------------------------------------------------------------------------
-- The action at one qubit
--
-- A dirty gate entering on the left is pushed through A, then through
-- C, then through E, collecting phases; ω is central, so the phases
-- accumulate onto the normal form's own ωᵖ regardless of where they
-- were emitted.

act : DirtA → NF 1 → NF 1
act d (((a , c) , e , tt) , p) with pushA d a
... | k₁ , a′ , oc with pushC* oc c
...   | k₂ , c′ , oe with pushE* oe e
...     | k₃ , e′ = ((a′ , c′) , e′ , tt) , k₁ + k₂ + k₃ + p

-- The scalar just steps the phase.
act-ω : NF 1 → NF 1
act-ω (b , p) = b , ₁ + p

------------------------------------------------------------------------
-- The action of a generator
--
-- Gen 1 holds the scalar (at any width), H and S, and the scalar again
-- one wire up -- the two spellings that Circuit.Base's ω↑=ω identifies,
-- which is why both step the phase.  A gate₂ would need two wires, so
-- that case is absent by its index.

actGen : Gen 1 → NF 1 → NF 1
actGen (gate₀ ω-gate)     = act-ω
actGen (gate₁ H-gate)     = act dH
actGen (gate₁ S-gate)     = act dS
actGen (gate₀ ω-gate ↥)   = act-ω
