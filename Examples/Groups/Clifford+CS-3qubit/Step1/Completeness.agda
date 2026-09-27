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
open import Presentation.Tactics.Reidemeister-Schreier using (module Reidemeister-Schreier-Simplified)
open Reidemeister-Schreier-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module TwoLevel)
open TwoLevel
open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less ; f ; completeness-property)
open TwoLevel-Less

module Examples.Groups.Clifford+CS-3qubit.Step1.Completeness where

-- The backward translation.
g : TwoLevel.Gen -> Word Gen
g = f

hypA : ∀ (x : Gen) -> TwoLevel-Less.Rel ⊢ [ x ]ʷ === (g ʷ) (f x)
hypA (i-gen x) = refl
hypA (X-gen jk) = refl
hypA (K-gen jk) = refl

lemma-[4] : ∀ {j k} -> {jk : Neq j k} -> TwoLevel-Less.Rel ⊢ i j • i k === i k • i j
lemma-[4] {jk = f<s x} = axiom ([4] {jk = x})
lemma-[4] {jk = f>s x} = symm (axiom ([4] {jk = x}))

lemma-[5] : ∀ {j k l} {kl : Less k l} -> {jk : Neq j k} -> {jl : Neq j l} -> TwoLevel-Less.Rel ⊢ i j • X kl === X kl • i j
lemma-[5] {kl = kl} {jk = f<s jk} {jl = f<s jl} = axiom ([5a] {kl = kl} {jk = jk})
lemma-[5] {kl = kl} {jk = f>s kj} {jl = f<s jl} = axiom ([5c] {kl = kl} {kj = kj} {jl = jl})
lemma-[5] {kl = kl} {jk = f<s jk} {jl = f>s lj} with anti-symmetry (transitivity jk kl) lj
... | ()
lemma-[5] {kl = kl} {jk = f>s kj} {jl = f>s lj} = axiom ([5b] {kl = kl} {lj = lj})

lemma-[6] : ∀ {j k l} {kl : Less k l} -> {jk : Neq j k} -> {jl : Neq j l} -> TwoLevel-Less.Rel ⊢ i j • K kl === K kl • i j
lemma-[6] {kl = kl} {jk = f<s jk} {jl = f<s jl} = axiom ([6a] {kl = kl} {jk = jk})
lemma-[6] {kl = kl} {jk = f>s kj} {jl = f<s jl} = axiom ([6c] {kl = kl} {kj = kj} {jl = jl})
lemma-[6] {kl = kl} {jk = f<s jk} {jl = f>s lj} with anti-symmetry (transitivity jk kl) lj
... | ()
lemma-[6] {kl = kl} {jk = f>s kj} {jl = f>s lj} = axiom ([6b] {kl = kl} {lj = lj})

lemma-[7] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Neq j l} -> {jm : Neq j m} -> {kl : Neq k l} -> {km : Neq k m} -> TwoLevel-Less.Rel ⊢ X jk • X lm === X lm • X jk
lemma-[7] {jk = jk} {lm} {jl} {f>s mj} {kl} {km} = axiom ([7a] {jk = jk} {lm} {mj})
lemma-[7] {jk = jk} {lm} {f>s lj} {f<s jm} {kl} {f>s mk} = axiom ([7b] {jk = jk} {lm} {jm} {mk} {lj})
lemma-[7] {jk = jk} {lm} {f<s jl} {f<s jm} {kl} {f>s mk} = axiom ([7c] {jk = jk} {lm} {jl} {mk} )
lemma-[7] {jk = jk} {lm} {jl} {jm} {f<s kl} {km} = symm (axiom ([7a] {jk = lm} {jk} {kl}))
lemma-[7] {jk = jk} {lm} {f<s jl} {jm} {f>s lk} {f<s km} = symm (axiom ([7b] {jk = lm} {jk} {lk} {km} {jl}))
lemma-[7] {jk = jk} {lm} {f>s lj} {jm} {f>s lk} {f<s km} = symm (axiom ([7c] {jk = lm} {jk} {lj} {km} ))


lemma-[8] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Neq j l} -> {jm : Neq j m} -> {kl : Neq k l} -> {km : Neq k m} -> TwoLevel-Less.Rel ⊢ X jk • K lm === K lm • X jk
lemma-[8] {jk = jk} {lm} {jl} {f>s mj} {kl} {km} = axiom ([8a] {jk = jk} {lm} {mj})
lemma-[8] {jk = jk} {lm} {f>s lj} {f<s jm} {kl} {f>s mk} = axiom ([8b] {jk = jk} {lm} {jm} {mk} {lj})
lemma-[8] {jk = jk} {lm} {f<s jl} {f<s jm} {kl} {f>s mk} = axiom ([8c] {jk = jk} {lm} {jl} {mk} )
lemma-[8] {jk = jk} {lm} {jl} {jm} {f<s kl} {km} = (axiom ([8e] {jk = jk} {lm} {kl}))
lemma-[8] {jk = jk} {lm} {f<s jl} {f<s jm} {f>s lk} {f<s km} = axiom ([8d] {jk = jk} {lm} {jl} {lk} {km})
lemma-[8] {jk = jk} {lm} {f>s lj} {jm} {f>s lk} {f<s km} = (axiom ([8f] {jk = jk} {lm} {lj} {km} ))

lemma-[9] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Neq j l} -> {jm : Neq j m} -> {kl : Neq k l} -> {km : Neq k m} -> TwoLevel-Less.Rel ⊢ K jk • K lm === K lm • K jk
lemma-[9] {jk = jk} {lm} {jl} {f>s mj} {kl} {km} = axiom ([9a] {jk = jk} {lm} {mj})
lemma-[9] {jk = jk} {lm} {f>s lj} {f<s jm} {kl} {f>s mk} = axiom ([9b] {jk = jk} {lm} {jm} {mk} {lj})
lemma-[9] {jk = jk} {lm} {f<s jl} {f<s jm} {kl} {f>s mk} = axiom ([9c] {jk = jk} {lm} {jl} {mk} )
lemma-[9] {jk = jk} {lm} {jl} {jm} {f<s kl} {km} = symm (axiom ([9a] {jk = lm} {jk} {kl}))
lemma-[9] {jk = jk} {lm} {f<s jl} {jm} {f>s lk} {f<s km} = symm (axiom ([9b] {jk = lm} {jk} {lk} {km} {jl}))
lemma-[9] {jk = jk} {lm} {f>s lj} {jm} {f>s lk} {f<s km} = symm (axiom ([9c] {jk = lm} {jk} {lj} {km} ))


lemma-[19] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} {jl : Less j l} {km : Less k m} {kl : Neq k l} -> TwoLevel-Less.Rel ⊢ K jk • K lm • K jl • K km === K jl • K km • K jk • K lm
lemma-[19] {jk = jk} {lm} {jl} {km} {f<s kl} = axiom ([19a] {jk = jk} {lm} {jl} {km} {kl})
lemma-[19] {jk = jk} {lm} {jl} {km} {f>s lk} = symm (axiom (([19a]) {jk = jl} {km} {jk} {lm} {lk}) )

hypB : ∀ {u t : Word TwoLevel.Gen} -> u === t ∈ TwoLevel.Rel -> TwoLevel-Less.Rel ⊢ (g ʷ) u === (g ʷ) t
hypB [1] = axiom [1]
hypB [2] = axiom [2]
hypB [3] = axiom [3]
hypB ([4] {jk = jk}) = lemma-[4] {jk = jk}
hypB ([5] {kl = kl} {jk} {jl}) = lemma-[5] {kl = kl} {jk} {jl}
hypB ([6] {kl = kl} {jk} {jl}) = lemma-[6] {kl = kl} {jk} {jl}
hypB ([7] {jk = jk} {lm} {jl} {jm} {kl} {km}) = lemma-[7] {jk = jk} {lm} {jl} {jm} {kl} {km}
hypB ([8] {jk = jk} {lm} {jl} {jm} {kl} {km}) = lemma-[8] {jk = jk} {lm} {jl} {jm} {kl} {km}
hypB ([9] {jk = jk} {lm} {jl} {jm} {kl} {km}) = lemma-[9] {jk = jk} {lm} {jl} {jm} {kl} {km}
hypB [10] = axiom [10]
hypB [11] = axiom [11]
hypB [12] = axiom [12]
hypB [13] = axiom [13]
hypB [14] = axiom [14]
hypB [15] = axiom [15]
hypB [16] = axiom [16]
hypB [17] = axiom [17]
hypB [18] = axiom [18]
hypB ([19] {jk = jk} {lm} {jl} {km} {lk}) = lemma-[19] {jk = jk} {lm} {jl} {km} {lk}

completeness : completeness-property
completeness {w} {v} = reidemeister-schreier-simplified f g hypA (\ x y -> hypB {x} {y}) w v
