------------------------------------------------------------------------
-- Presentations of groups
--
-- This module contains the statement of the main theorem. It contains
-- four things:
--
-- * Our generators and relations for the monoid U₈(ℤ[1/2, i]), from
--   Figure 1. These were proven to be sound and complete in
--   arXiv:2204.02217. We do not reprove the results of
--   arXiv:2204.02217 here, but rather we use them as a starting
--   point.
--
-- * Our generators and relations for 3-qubit Clifford+CS circuits,
--   from Figure 2.
--
-- * A translation from the Clifford+CS generators to the 2-level
--   generators.
--
-- * The statement of the soundness and completeness theorems, namely:
--   an equation is derivable from our Clifford+CS axioms if and only
--   if it is derivable from the 2-level axioms (and therefore, by
--   the result of arXiv:2204.02217, if and only if it is true).
--
-- This module contains the *statement* of the soundness and
-- completeness theorems, to ensure that these theorems do not depend
-- on any definitions other than what is stated or imported here.
--
-- The *proof* of the soundness and completeness theorems require many
-- additional definitions, lemmas, and computations, and is
-- distributed over a large number of files. The final machine-checked
-- proofs can be found in Proof.agda.
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Word.Base
open import Presentation.Tactics.Judgement
open import Examples.Groups.Clifford+CS-3qubit.Index

module Examples.Groups.Clifford+CS-3qubit.Theorem where

-- ----------------------------------------------------------------------
-- * Generators and relations for U₈(ℤ[1/2, i])

module TwoLevel where
  -- 2-level generators.
  data Gen : Set where
    i-gen : Index -> Gen
    X-gen : ∀ {j k : Index} (jk : Less j k) -> Gen
    K-gen : ∀ {j k : Index} (jk : Less j k) -> Gen

  -- For convenience, we define a singleton word for every generator.
  i : ∀ (j : Index) -> Word Gen
  i j = [ i-gen j ]ʷ

  X : ∀ {j k : Index} (jk : Less j k) -> Word Gen
  X {j = j} {k = k} jk = [ X-gen {j = j} {k = k} jk ]ʷ

  K : ∀ {j k : Index} (jk : Less j k) -> Word Gen
  K {j = j} {k = k} jk = [ K-gen {j = j} {k = k} jk ]ʷ

  -- 2-level relations.
  data Rel : Context Gen where
    -- (a) Order of generators:
    [1] : ∀ {j : Index} -> i j ^ 4 === ε ∈ Rel
    [2] : ∀ {j k : Index} {jk : Less j k} -> X jk ^ 2 === ε ∈ Rel
    [3] : ∀ {j k : Index} {jk : Less j k} -> K jk ^ 8 === ε ∈ Rel

    -- (b) Disjoint generators commute:
    [4] : ∀ {j k} -> {jk : Neq j k} -> i j • i k === i k • i j ∈ Rel
    [5] : ∀ {j k l} {kl : Less k l} -> {jk : Neq j k} -> {jl : Neq j l} -> i j • X kl === X kl • i j ∈ Rel
    [6] : ∀ {j k l} {kl : Less k l} -> {jk : Neq j k} -> {jl : Neq j l} -> i j • K kl === K kl • i j ∈ Rel
    [7] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Neq j l} -> {jm : Neq j m} -> {kl : Neq k l} -> {km : Neq k m} -> X jk • X lm === X lm • X jk ∈ Rel
    [8] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Neq j l} -> {jm : Neq j m} -> {kl : Neq k l} -> {km : Neq k m} -> X jk • K lm === K lm • X jk ∈ Rel
    [9] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Neq j l} -> {jm : Neq j m} -> {kl : Neq k l} -> {km : Neq k m} -> K jk • K lm === K lm • K jk ∈ Rel

    -- (c) X permutes indices:
    [10] : ∀ {j k} {jk : Less j k} -> i k • X jk === X jk • i j  ∈ Rel
    [11] : ∀ {j k l} {kl : Less k l} {jk : Less j k} {jl : Less j l} -> X kl • X jk === X jk • X jl ∈ Rel
    [12] : ∀ {j k l} {jl : Less j l} {kl : Less k l} {jk : Less j k} -> X jl • X kl === X kl • X jk ∈ Rel
    [13] : ∀ {j k l} {kl : Less k l} {jk : Less j k} {jl : Less j l} -> K kl • X jk === X jk • K jl ∈ Rel
    [14] : ∀ {j k l} {jl : Less j l} {kl : Less k l} {jk : Less j k} -> K jl • X kl === X kl • K jk ∈ Rel

    -- (d)  additional properties of the generators.
    [15] : ∀ {j k} {jk : Less j k} -> K jk • i k ^ 2 === X jk • K jk ∈ Rel
    [16] : ∀ {j k} {jk : Less j k} -> K jk • i k ^ 3 === i k • K jk • i k • K jk ∈ Rel
    [17] : ∀ {j k} {jk : Less j k} -> K jk • i j • i k === i j • i k • K jk ∈ Rel

    [18] : ∀ {j k} {jk : Less j k} -> K jk ^ 2 • i j • i k === ε ∈ Rel
    [19] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} {jl : Less j l} {km : Less k m} {kl : Neq k l} -> K jk • K lm • K jl • K km === K jl • K km • K jk • K lm ∈ Rel

-- ----------------------------------------------------------------------
-- * Generators and relations for Clifford+CS

module CliffordCS where

  data Gen : Set where
    S0-gen : Gen
    S1-gen : Gen
    S2-gen : Gen
    CS01-gen : Gen
    CS12-gen : Gen
    iI-gen : Gen
    K0-gen : Gen
    K1-gen : Gen
    K2-gen : Gen

  -- Abbreviations.
  S0 : Word Gen
  S0 = [ S0-gen ]ʷ

  S1 : Word Gen
  S1 = [ S1-gen ]ʷ

  S2 : Word Gen
  S2 = [ S2-gen ]ʷ

  CS01 : Word Gen
  CS01 = [ CS01-gen ]ʷ
  CS10 = CS01

  CS12 : Word Gen
  CS12 = [ CS12-gen ]ʷ
  CS21 = CS12

  iI : Word Gen
  iI = [ iI-gen ]ʷ

  K0 : Word Gen
  K0 = [ K0-gen ]ʷ

  K1 : Word Gen
  K1 = [ K1-gen ]ʷ

  K2 : Word Gen
  K2 = [ K2-gen ]ʷ

  X0 : Word Gen
  X0 = K0 • S0 • S0 • K0 • iI

  X1 : Word Gen
  X1 = K1 • S1 • S1 • K1 • iI

  X2 : Word Gen
  X2 = K2 • S2 • S2 • K2 • iI

  CX01 : Word Gen
  CX01 = K1 • CS01 • CS01 • K1 • iI

  CX10 : Word Gen
  CX10 = K0 • CS10 • CS10 • K0 • iI

  CX12 : Word Gen
  CX12 = K2 • CS12 • CS12 • K2 • iI

  CX21 : Word Gen
  CX21 = K1 • CS21 • CS21 • K1 • iI

  Swap01 : Word Gen
  Swap01 = CX01 • CX10 • CX01

  Swap12 : Word Gen
  Swap12 = CX12 • CX21 • CX12

  CS02 : Word Gen
  CS02 = Swap12 • CS01 • Swap12
  CS20 = CS02

  CCZ : Word Gen
  CCZ = CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21


  CCX0 : Word Gen
  CCX0 = K0 • CCZ • K0 • iI

  CCX1 : Word Gen
  CCX1 = K1 • CCZ • K1 • iI

  CCX2 : Word Gen
  CCX2 = K2 • CCZ • K2 • iI

  CX02 : Word Gen
  CX02 = K2 • CS02 • CS02 • K2 • iI

  CX20 : Word Gen
  CX20 = K0 • CS02 • CS02 • K0 • iI

  CCK' : Word Gen
  CCK' = K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI

  CK10 : Word Gen
  CK10 = CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI

  CK21 : Word Gen
  CK21 = CS12 • K1 • CS12 • K1 • CS12 • S2 • S2 • S2 • iI

  CK20 : Word Gen
  CK20 = CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI

  data Rel : Context Gen where
    ax-iI-iI-iI-iI=ε : iI • iI • iI • iI === ε ∈ Rel
    ax-iI-S0=S0-iI : iI • S0 === S0 • iI ∈ Rel
    ax-iI-S1=S1-iI : iI • S1 === S1 • iI ∈ Rel
    ax-iI-S2=S2-iI : iI • S2 === S2 • iI ∈ Rel
    ax-iI-K0=K0-iI : iI • K0 === K0 • iI ∈ Rel
    ax-iI-K1=K1-iI : iI • K1 === K1 • iI ∈ Rel
    ax-iI-K2=K2-iI : iI • K2 === K2 • iI ∈ Rel
    ax-iI-CS01=CS01-iI : iI • CS01 === CS01 • iI ∈ Rel
    ax-iI-CS12=CS12-iI : iI • CS12 === CS12 • iI ∈ Rel

    ax-S1-S0=S0-S1 : S1 • S0 === S0 • S1 ∈ Rel
    ax-S2-S0=S0-S2 : S2 • S0 === S0 • S2 ∈ Rel
    ax-S2-S1=S1-S2 : S2 • S1 === S1 • S2 ∈ Rel
    ax-K1-K0=K0-K1 : K1 • K0 === K0 • K1 ∈ Rel
    ax-K2-K0=K0-K2 : K2 • K0 === K0 • K2 ∈ Rel
    ax-K2-K1=K1-K2 : K2 • K1 === K1 • K2 ∈ Rel
    ax-CS01-S0=S0-CS01 : CS01 • S0 === S0 • CS01 ∈ Rel
    ax-CS12-S0=S0-CS12 : CS12 • S0 === S0 • CS12 ∈ Rel
    ax-CS01-S1=S1-CS01 : CS01 • S1 === S1 • CS01 ∈ Rel
    ax-CS12-S1=S1-CS12 : CS12 • S1 === S1 • CS12 ∈ Rel
    ax-CS01-S2=S2-CS01 : CS01 • S2 === S2 • CS01 ∈ Rel
    ax-CS12-S2=S2-CS12 : CS12 • S2 === S2 • CS12 ∈ Rel
    ax-CS12-CS01=CS01-CS12 : CS12 • CS01 === CS01 • CS12 ∈ Rel

    ax-S1-K0=K0-S1 : S1 • K0 === K0 • S1 ∈ Rel
    ax-S2-K0=K0-S2 : S2 • K0 === K0 • S2 ∈ Rel
    ax-S2-K1=K1-S2 : S2 • K1 === K1 • S2 ∈ Rel
    ax-K1-S0=S0-K1 : K1 • S0 === S0 • K1 ∈ Rel
    ax-K2-S0=S0-K2 : K2 • S0 === S0 • K2 ∈ Rel
    ax-K2-S1=S1-K2 : K2 • S1 === S1 • K2 ∈ Rel
    ax-CS01-K2=K2-CS01 : CS01 • K2 === K2 • CS01 ∈ Rel
    ax-CS12-K0=K0-CS12 : CS12 • K0 === K0 • CS12 ∈ Rel

    ax-S0-S0-S0-S0=ε : S0 • S0 • S0 • S0 === ε ∈ Rel
    ax-S1-S1-S1-S1=ε : S1 • S1 • S1 • S1 === ε ∈ Rel
    ax-S2-S2-S2-S2=ε : S2 • S2 • S2 • S2 === ε ∈ Rel
    ax-CS01-CS01-CS01-CS01=ε : CS01 • CS01 • CS01 • CS01 === ε ∈ Rel
    ax-CS12-CS12-CS12-CS12=ε : CS12 • CS12 • CS12 • CS12 === ε ∈ Rel


    ax-K0-K0=iI-iI-iI : K0 • K0 === iI • iI • iI ∈ Rel
    ax-K1-K1=iI-iI-iI : K1 • K1 === iI • iI • iI ∈ Rel
    ax-K2-K2=iI-iI-iI : K2 • K2 === iI • iI • iI ∈ Rel
    ax-S0-K0-S0-K0-S0-K0=iI-iI-iI : S0 • K0 • S0 • K0 • S0 • K0 === iI • iI • iI ∈ Rel
    ax-S1-K1-S1-K1-S1-K1=iI-iI-iI : S1 • K1 • S1 • K1 • S1 • K1 === iI • iI • iI ∈ Rel
    ax-S2-K2-S2-K2-S2-K2=iI-iI-iI : S2 • K2 • S2 • K2 • S2 • K2 === iI • iI • iI ∈ Rel

    --X-CS
    ax-X0-CS01=CS01-CS01-CS01-X0-S1 : X0 • CS01 === CS01 • CS01 • CS01 • X0 • S1 ∈ Rel
    ax-X1-CS01=CS01-CS01-CS01-X1-S0 : X1 • CS01 === CS01 • CS01 • CS01 • X1 • S0 ∈ Rel
    ax-X1-CS12=CS12-CS12-CS12-X1-S2 : X1 • CS12 === CS12 • CS12 • CS12 • X1 • S2 ∈ Rel
    ax-X2-CS12=CS12-CS12-CS12-X2-S1 : X2 • CS12 === CS12 • CS12 • CS12 • X2 • S1 ∈ Rel

    ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 : CS01 • K0 • CS01 • K0 • S0 === S0 • K0 • CS01 • K0 • CS01 ∈ Rel
    ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01 : CS01 • K1 • CS01 • K1 • S1 === S1 • K1 • CS01 • K1 • CS01 ∈ Rel
    ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12 : CS12 • K1 • CS12 • K1 • S1 === S1 • K1 • CS12 • K1 • CS12 ∈ Rel
    ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12 : CS12 • K2 • CS12 • K2 • S2 === S2 • K2 • CS12 • K2 • CS12 ∈ Rel
    ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12 : CX10 • CX01 • CS12 • CX01 • CX10 === CX12 • CX21 • CS01 • CX21 • CX12 ∈ Rel
    ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12 : CX10 • CX01 • CS12 • CS12 • CX01 • CX10 === CX01 • CS12 • CS12 • CX01 • CS12 • CS12 ∈ Rel
    ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21 : CS12 • CX01 • CS12 • CS12 • CS12 • CX01 === CS01 • CX21 • CS01 • CS01 • CS01 • CX21 ∈ Rel
    ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12 : CS12 • K1 • CS12 • K1 • CS01 • K1 • CS01 === CS01 • K1 • CS01 • K1 • CS12 • K1 • CS12 ∈ Rel
    ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1 : CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12 === CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS01 ∈ Rel


-- ----------------------------------------------------------------------
-- * Translation from Clifford+CS generators to 2-level generators

open TwoLevel
open CliffordCS

f : CliffordCS.Gen -> Word TwoLevel.Gen
f S0-gen = i ₄ • i ₅ • i ₆ • i ₇
f S1-gen = i ₂ • i ₃ • i ₆ • i ₇
f S2-gen = i ₁ • i ₃ • i ₅ • i ₇
f CS01-gen = i ₆ • i ₇
f CS12-gen = i ₃ • i ₇
f iI-gen = i ₀ • i ₁ • i ₂ • i ₃ • i ₄ • i ₅ • i ₆ • i ₇
f K0-gen = K ₀₄ • K ₁₅ • K ₂₆ • K ₃₇
f K1-gen = K ₀₂ • K ₁₃ • K ₄₆ • K ₅₇
f K2-gen = K ₀₁ • K ₂₃ • K ₄₅ • K ₆₇

-- ----------------------------------------------------------------------
-- * Statement of soundness and completeness.

-- The proofs follow later, but we give the statements here, to ensure
-- they only depend on the definitions already given.

soundness-property : Set
soundness-property = ∀ {w v} -> CliffordCS.Rel ⊢ w === v -> TwoLevel.Rel ⊢ (f ʷ) w === (f ʷ) v

completeness-property : Set
completeness-property = ∀ {w v} -> TwoLevel.Rel ⊢ (f ʷ) w === (f ʷ) v -> CliffordCS.Rel ⊢ w === v
