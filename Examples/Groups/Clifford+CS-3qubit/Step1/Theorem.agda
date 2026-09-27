------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base
open import Presentation.Tactics.Judgement

open import Examples.Groups.Clifford+CS-3qubit.Index
open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module TwoLevel)

module Examples.Groups.Clifford+CS-3qubit.Step1.Theorem where

module TwoLevel-Less where

  -- Reuse the 2-level generators Gen and abbreviations in TwoLevel as
  -- the generators and abbreviations here.
  open TwoLevel hiding (Rel) public

  -- 2-level relations using only less.
  data Rel : Context Gen where

    -- (a) Order of generators:
    [1] : ∀ {j : Index} -> i j ^ 4 === ε ∈ Rel
    [2] : ∀ {j k : Index} {jk : Less j k} -> X jk ^ 2 === ε ∈ Rel
    [3] : ∀ {j k : Index} {jk : Less j k} -> K jk ^ 8 === ε ∈ Rel

    -- (b) Disjoint generators commute:
    [4] : ∀ {j k} -> {jk : Less j k} -> i j • i k === i k • i j ∈ Rel
    [5a] : ∀ {j k l} {kl : Less k l} -> {jk : Less j k} -> i j • X kl === X kl • i j ∈ Rel
    [5b] : ∀ {j k l} {kl : Less k l} -> {lj : Less l j} -> i j • X kl === X kl • i j ∈ Rel
    [5c] : ∀ {j k l} {kl : Less k l} -> {kj : Less k j} -> {jl : Less j l} -> i j • X kl === X kl • i j ∈ Rel
    [6a] : ∀ {j k l} {kl : Less k l} -> {jk : Less j k} -> i j • K kl === K kl • i j ∈ Rel
    [6b] : ∀ {j k l} {kl : Less k l} -> {lj : Less l j} -> i j • K kl === K kl • i j ∈ Rel
    [6c] : ∀ {j k l} {kl : Less k l} -> {kj : Less k j} -> {jl : Less j l} -> i j • K kl === K kl • i j ∈ Rel

    [7a] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {mj : Less m j} -> X jk • X lm === X lm • X jk ∈ Rel
    [7b] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jm : Less j m} -> {mk : Less m k} -> {lj : Less l j} -> X jk • X lm === X lm • X jk ∈ Rel
    [7c] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Less j l} -> {mk : Less m k} -> X jk • X lm === X lm • X jk ∈ Rel

    [8a] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {mj : Less m j} -> X jk • K lm === K lm • X jk ∈ Rel
    [8b] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jm : Less j m} -> {mk : Less m k} -> {lj : Less l j} -> X jk • K lm === K lm • X jk ∈ Rel
    [8c] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Less j l} -> {mk : Less m k} -> X jk • K lm === K lm • X jk ∈ Rel
    [8d] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Less j l} -> {lk : Less l k} -> {km : Less k m} -> X jk • K lm === K lm • X jk ∈ Rel
    [8e] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {kl : Less k l} -> X jk • K lm === K lm • X jk ∈ Rel
    [8f] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {lj : Less l j} -> {km : Less k m} -> X jk • K lm === K lm • X jk ∈ Rel


    [9a] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {mj : Less m j} -> K jk • K lm === K lm • K jk ∈ Rel
    [9b] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jm : Less j m} -> {mk : Less m k} -> {lj : Less l j} -> K jk • K lm === K lm • K jk ∈ Rel
    [9c] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Less j l} -> {mk : Less m k} -> K jk • K lm === K lm • K jk ∈ Rel

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
    [19a] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} {jl : Less j l} {km : Less k m} {kl : Less k l} -> K jk • K lm • K jl • K km === K jl • K km • K jk • K lm ∈ Rel

    -- Note: [19b] is [19a] reversed. [19a] and [19b] are [19] in the paper.
    {-
    [19b] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} {jl : Less j l} {km : Less k m} {lk : Less l k} -> K jk • K lm • K jl • K km === K jl • K km • K jk • K lm ∈ Rel
    -}
    
open TwoLevel-Less
open TwoLevel

-- Two sets of relations on the same generators. The translation is
-- the identity.
f : Gen -> Word TwoLevel.Gen
f x = [ x ]ʷ

soundness-property : Set
soundness-property = TwoLevel-Less.Rel is-sound-wrt TwoLevel.Rel and f

completeness-property : Set
completeness-property = TwoLevel-Less.Rel is-complete-wrt TwoLevel.Rel and f
