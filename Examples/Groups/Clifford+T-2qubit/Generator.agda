------------------------------------------------------------------------
-- Presentations of groups
--
-- Generators and relations for 2-qubit Clifford+T operators (Bian and
-- Selinger, "Generators and relations for 2-qubit Clifford+T
-- operators", Figure 1), Greylyn's generators and relations for
-- U₄(ℤ[1/√2,i]) with indices 0–3 (Figure 3), and the translation f of
-- the former into the latter.  Ported from the Agda code accompanying
-- the paper (CC BY 2.0).
--
-- Soundness (Clifford+T derivations translate to Greylyn derivations)
-- and completeness (the converse) are stated here and proved in
-- Soundness and Completeness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Generator where

open import Data.Nat.Base using (ℕ)

open import Word.Base
open import Presentation.Tactics.Judgement


-- ----------------------------------------------------------------------
-- * Generators and relations for 2-qubit Clifford+T circuits

module Clifford+T where

  infix 5 Rel

  -- The generators.
  data Generator : Set where
    W-gen : Generator
    H0-gen : Generator
    H1-gen : Generator
    S0-gen : Generator
    S1-gen : Generator
    T0-gen : Generator
    T1-gen : Generator
    CZ-gen : Generator

  -- For convenience, we define a singleton word for each generator.
  W : Word Generator
  W = [ W-gen ]ʷ

  H0 : Word Generator
  H0 = [ H0-gen ]ʷ

  H1 : Word Generator
  H1 = [ H1-gen ]ʷ

  S0 : Word Generator
  S0 = [ S0-gen ]ʷ

  S1 : Word Generator
  S1 = [ S1-gen ]ʷ

  T0 : Word Generator
  T0 = [ T0-gen ]ʷ

  T1 : Word Generator
  T1 = [ T1-gen ]ʷ

  CZ : Word Generator
  CZ = [ CZ-gen ]ʷ

  -- For added convenience, we also define abbreviations for X0 and X1,
  -- various inverses, and controlled gates.
  X0 : Word Generator
  X0 = H0 • S0 • S0 • H0

  X1 : Word Generator
  X1 = H1 • S1 • S1 • H1

  W⁻¹ : Word Generator
  W⁻¹ = W ^ 7

  T0⁻¹ : Word Generator
  T0⁻¹ = T0 ^ 7

  T1⁻¹ : Word Generator
  T1⁻¹ = T1 ^ 7

  S0⁻¹ : Word Generator
  S0⁻¹ = S0 ^ 3

  S1⁻¹ : Word Generator
  S1⁻¹ = S1 ^ 3

  -- Controlled X0-gate.
  CX0 : Word Generator
  CX0 = H0 • CZ • H0

  -- Controlled X1-gate.
  CX1 : Word Generator
  CX1 = H1 • CZ • H1

  -- Controlled H0-gate.
  CH0 : Word Generator
  CH0 = S0 • H0 • T0 • CX0 • T0⁻¹ • H0 • S0⁻¹

  -- Controlled H1-gate.
  CH1 : Word Generator
  CH1 = S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹

  -- The swap gate.
  Swap : Word Generator
  Swap = H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0

  -- The relations from Figure 1.
  data Rel : Context Generator where
    
    -- (a) Monoidal relations:
    comm-W : ∀ g -> W • [ g ]ʷ === [ g ]ʷ • W ∈ Rel
    comm-H0-H1 : H0 • H1 === H1 • H0 ∈ Rel
    comm-H0-S1 : H0 • S1 === S1 • H0 ∈ Rel
    comm-H0-T1 : H0 • T1 === T1 • H0 ∈ Rel
    comm-S0-H1 : S0 • H1 === H1 • S0 ∈ Rel
    comm-S0-S1 : S0 • S1 === S1 • S0 ∈ Rel
    comm-S0-T1 : S0 • T1 === T1 • S0 ∈ Rel
    comm-T0-H1 : T0 • H1 === H1 • T0 ∈ Rel
    comm-T0-S1 : T0 • S1 === S1 • T0 ∈ Rel
    comm-T0-T1 : T0 • T1 === T1 • T0 ∈ Rel

    -- (b) Order of Clifford group elements:
    order-W : W ^ 8 === ε ∈ Rel
    order-H0 : H0 ^ 2 === ε ∈ Rel
    order-H1 : H1 ^ 2 === ε ∈ Rel
    order-S0 : S0 ^ 4 === ε ∈ Rel
    order-S1 : S1 ^ 4 === ε ∈ Rel
    order-S0H0 : (S0 • H0) ^ 3 === W ∈ Rel
    order-S1H1 : (S1 • H1) ^ 3 === W ∈ Rel
    order-CZ : CZ ^ 2 === ε ∈ Rel

    -- (c) Remaining Clifford relations:
    comm-S0-CZ : S0 • CZ === CZ • S0 ∈ Rel
    comm-S1-CZ : S1 • CZ === CZ • S1 ∈ Rel
    rel-X0-CZ : X0 • CZ === CZ • S1 • S1 • X0 ∈ Rel
    rel-X1-CZ : X1 • CZ === CZ • S0 • S0 • X1 ∈ Rel
    rel-CZ-H0-CZ : CZ • H0 • CZ === S0 • H0 • CZ • S0 • H0 • S0 • S1 • W⁻¹ ∈ Rel
    rel-CZ-H1-CZ : CZ • H1 • CZ === S1 • H1 • CZ • S1 • H1 • S1 • S0 • W⁻¹ ∈ Rel

    -- (d) "Obvious" relations involving T:
    square-T0 : T0 ^ 2 === S0 ∈ Rel
    square-T1 : T1 ^ 2 === S1 ∈ Rel
    lemma-order-T0X0 : (T0 • X0) ^ 2 === W ∈ Rel
    lemma-order-T1X1 : (T1 • X1) ^ 2 === W ∈ Rel
    comm-T0-CZ : T0 • CZ === CZ • T0 ∈ Rel
    -- Note: comm-T1-CZ is derivable; see lemma-comm-T1-CZ.
    swap-T0 : H1 • CZ • H0 • H1 • CZ • H0 • T0 === T1 • H1 • CZ • H0 • H1 • CZ • H0 ∈ Rel

    -- (e) "Non-obvious" relations involving T:
    rel-A : CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ === T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 ∈ Rel
    rel-B : CX1 • T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ === T1 • H1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • H1 • T1⁻¹ • CX1 ∈ Rel
    rel-C : CH1 • H1 • T1 • CH1 • CH0 • H0 • T0 • CH0 === CH0 • H0 • T0 • CH0 • CH1 • H1 • T1 • CH1 ∈ Rel

-- ----------------------------------------------------------------------
-- * Generators and relations for U₄(Z[1/√2, i]) from Greylyn's thesis

module Greylyn where

  -- Indices range from 0 to 3.
  data Index : Set where
    ₀ : Index
    ₁ : Index
    ₂ : Index
    ₃ : Index

  -- The less-than relation on indices.
  data Less : Index -> Index -> Set where
    ₀₁ : Less ₀ ₁
    ₀₂ : Less ₀ ₂
    ₀₃ : Less ₀ ₃
    ₁₂ : Less ₁ ₂
    ₁₃ : Less ₁ ₃
    ₂₃ : Less ₂ ₃

  -- The not-equal relation on indices.
  data Neq : Index -> Index -> Set where
    ₀₁ : Neq ₀ ₁
    ₀₂ : Neq ₀ ₂
    ₀₃ : Neq ₀ ₃
    ₁₂ : Neq ₁ ₂
    ₁₃ : Neq ₁ ₃
    ₂₃ : Neq ₂ ₃
    ₁₀ : Neq ₁ ₀
    ₂₀ : Neq ₂ ₀
    ₃₀ : Neq ₃ ₀
    ₂₁ : Neq ₂ ₁
    ₃₁ : Neq ₃ ₁
    ₃₂ : Neq ₃ ₂

  -- Greylyn's generators.
  data Generator : Set where
    ω-gen : (j : Index) -> Generator
    X-gen : ∀ {j k} -> (jk : Less j k) -> Generator
    H-gen : ∀ {j k} -> (jk : Less j k) -> Generator

  -- For convenience, we define a singleton word for every generator.
  ω : (j : Index) -> Word Generator
  ω j = [ ω-gen j ]ʷ

  X : ∀ {j k} (jk : Less j k) -> Word Generator
  X jk = [ X-gen jk ]ʷ

  H : ∀ {j k} (jk : Less j k) -> Word Generator
  H jk = [ H-gen jk ]ʷ

  -- Greylyn's relations.
  data Rel : Context Generator where
  
    -- (a) Order of generators:
    [1] : ∀ {j} -> ω j ^ 8 === ε ∈ Rel
    [2] : ∀ {j k} {jk : Less j k} -> H jk ^ 2 === ε ∈ Rel
    [3] : ∀ {j k} {jk : Less j k} -> X jk ^ 2 === ε ∈ Rel

    -- (b) Disjoint generators commute:
    [4] : ∀ {j k} -> {jk : Neq j k} -> ω j • ω k === ω k • ω j ∈ Rel
    [5] : ∀ {j k l} {jk : Less j k} -> {lj : Neq l j} -> {lk : Neq l k} -> ω l • H jk === H jk • ω l ∈ Rel
    [6] : ∀ {j k l} {jk : Less j k} -> {lj : Neq l j} -> {lk : Neq l k} -> ω l • X jk === X jk • ω l ∈ Rel
    [7] : ∀ {j k l t} {jk : Less j k} {lt : Less l t} -> {lj : Neq l j} -> {lk : Neq l k} -> {tj : Neq t j} -> {tk : Neq t k} -> H jk • H lt === H lt • H jk ∈ Rel
    [8] : ∀ {j k l t} {jk : Less j k} {lt : Less l t} -> {lj : Neq l j} -> {lk : Neq l k} -> {tj : Neq t j} -> {tk : Neq t k} -> H jk • X lt === X lt • H jk ∈ Rel
    [9] : ∀ {j k l t} {jk : Less j k} {lt : Less l t} -> {lj : Neq l j} -> {lk : Neq l k} -> {tj : Neq t j} -> {tk : Neq t k} -> X jk • X lt === X lt • X jk ∈ Rel

    -- (c) X permutes indices:
    [10] : ∀ {j k} {jk : Less j k} -> X jk • ω k === ω j • X jk ∈ Rel
    [11] : ∀ {j k} {jk : Less j k} -> X jk • ω j === ω k • X jk ∈ Rel
    [12] : ∀ {j k l} {jk : Less j k} {kl : Less k l} {jl : Less j l} -> X jk • X jl === X kl • X jk ∈ Rel
    [13] : ∀ {j k l} {jk : Less j k} {lk : Less l k} {lj : Less l j} -> X jk • X lj === X lk • X jk ∈ Rel
    [14] : ∀ {j k l} {jk : Less j k} {kl : Less k l} {jl : Less j l} -> X jk • H jl === H kl • X jk ∈ Rel
    [15] : ∀ {j k l} {jk : Less j k} {lk : Less l k} {lj : Less l j} -> X jk • H lj === H lk • X jk ∈ Rel

    -- (d) ω[j]ω[k] is diagonal:
    [16] : ∀ {j k} {jk : Less j k} -> ω j • ω k • X jk === X jk • ω j • ω k ∈ Rel
    [17] : ∀ {j k} {jk : Less j k} -> ω j • ω k • H jk === H jk • ω j • ω k ∈ Rel

    -- (e) Relations for H:
    [18] : ∀ {j k} {jk : Less j k} -> H jk • X jk === ω k ^ 4 • H jk ∈ Rel
    [19] : ∀ {j k} {jk : Less j k} -> H jk • ω j ^ 2 • H jk === ω j ^ 6 • H jk • ω j ^ 3 • ω k ^ 5 ∈ Rel
    [20] : ∀ {j k l t} {jk : Less j k} {kl : Less k l} {lt : Less l t} {jl : Less j l} {kt : Less k t} -> H jk • H lt • H jl • H kt === H jl • H kt • H jk • H lt ∈ Rel

-- ----------------------------------------------------------------------
-- * Translation from Clifford+T generators to Greylyn generators

open Greylyn 
open Clifford+T

f : Clifford+T.Generator -> Word Greylyn.Generator
f W-gen = ω ₀ • ω ₁ • ω ₂ • ω ₃
f H0-gen = H ₁₃ • H ₀₂
f H1-gen = H ₂₃ • H ₀₁
f S0-gen = ω ₂ ^ 2 • ω ₃ ^ 2
f S1-gen = ω ₁ ^ 2 • ω ₃ ^ 2
f T0-gen = ω ₂ • ω ₃
f T1-gen = ω ₁ • ω ₃
f CZ-gen = ω ₃ ^ 4

-- ----------------------------------------------------------------------
-- * Statement of soundness and completeness.

-- The proofs follow later, but we give the statements here, to ensure
-- they only depend on the definitions already given.

soundness-property : Set
soundness-property = ∀ {w v} -> Clifford+T.Rel ⊢ w === v -> Greylyn.Rel ⊢ (f ʷ) w === (f ʷ) v

completeness-property : Set
completeness-property = ∀ {w v} -> Greylyn.Rel ⊢ (f ʷ) w === (f ʷ) v -> Clifford+T.Rel ⊢ w === v
