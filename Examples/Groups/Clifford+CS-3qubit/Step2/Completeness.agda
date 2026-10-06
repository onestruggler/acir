------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
--
-- The original was checked with --call-by-name, which saved memory
-- while the rewrite loops of Presentation.Tactics.Words returned their
-- unevaluated argument.  With those loops fixed, call-by-name only
-- loses sharing, and the default call-by-need is much faster.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Reidemeister-Schreier using (module Reidemeister-Schreier-Simplified)
open Reidemeister-Schreier-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)
open TwoLevel-Less
open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified ; f ; g ; completeness-property)
open TwoLevel-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Simplified-Lemmas
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax1
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax2
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax3
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax4
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax5
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax6
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax7a
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax7b
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax7c
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8a
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8b
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8c
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8d
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8e
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8f
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax9a
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax9b
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax9c
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax10
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax11
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax12
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax13
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax14
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax15
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax16
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax17
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax18
open import Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax19a

module Examples.Groups.Clifford+CS-3qubit.Step2.Completeness where

hypA : ∀ (x : TwoLevel-Simplified.Gen) -> TwoLevel-Simplified.Rel ⊢ [ x ]ʷ === (g ʷ) (f x)
hypA i₀-gen = refl
hypA K₀₁-gen = refl
hypA X₀₁-gen = refl
hypA X₁₂-gen = refl
hypA X₂₃-gen = refl
hypA X₃₄-gen = refl
hypA X₄₅-gen = refl
hypA X₅₆-gen = refl
hypA X₆₇-gen = refl

hypB : ∀ (u t : Word TwoLevel-Less.Gen) -> u === t ∈ TwoLevel-Less.Rel -> TwoLevel-Simplified.Rel ⊢ (g ʷ) u === (g ʷ) t

hypB _ _ ([1] {j}) = lemma-[1] {j}
hypB _ _ ([2] {jk = jk}) = lemma-[2] {jk = jk}
hypB _ _ ([3] {jk = jk}) = lemma-[3] {jk = jk}
hypB _ _ ([4] {jk = jk}) = lemma-[4] {jk = jk}
hypB _ _ ([5a] {kl = kl} {jk}) = lemma-[5a] {kl = kl} {jk = jk}
hypB _ _ ([5b] {kl = kl} {lj}) = lemma-[5b] {kl = kl} {lj = lj}
hypB _ _ ([5c] {j} {k} {l} {kl} {kj} {jl}) = lemma-[5c] {j} {k} {l} {kl} {kj} {jl}
hypB _ _ ([6a] {kl = kl} {jk}) = lemma-[6a] {kl = kl} {jk}
hypB _ _ ([6b] {kl = kl} {lj}) = lemma-[6b] {kl = kl} {lj}
hypB _ _ ([6c] {kl = kl} {kj} {jl}) = lemma-[6c] {kl = kl} {kj} {jl}
hypB _ _ ([7a] {jk = jk} {lm} {mj}) = lemma-[7a] {jk = jk} {lm} {mj}
hypB _ _ ([7b] {jk = jk} {lm} {jm} {mk} {lj}) = lemma-[7b] {jk = jk} {lm} {jm} {mk} {lj}
hypB _ _ ([7c] {jk = jk} {lm} {jl} {mk}) = lemma-[7c] {jk = jk} {lm} {jl} {mk}
hypB _ _ ([8a] {jk = jk} {lm} {mj}) = lemma-[8a] {jk = jk} {lm} {mj}
hypB _ _ ([8b] {jk = jk} {lm} {jm} {mk} {lj}) = lemma-[8b] {jk = jk} {lm} {jm} {mk} {lj}
hypB _ _ ([8c] {jk = jk} {lm} {jl} {mk}) = lemma-[8c] {jk = jk} {lm} {jl} {mk}
hypB _ _ ([8d] {jk = jk} {lm} {jm} {mk} {lj}) = lemma-[8d] {jk = lm} {jk} {mk} {lj} {jm}
hypB _ _ ([8e] {jk = jk} {lm} {jm}) = lemma-[8e] {jk = lm} {jk} {jm}
hypB _ _ ([8f] {jk = jk} {lm = lm} {lj} {km}) = lemma-[8b'] {jk = lm} {lm = jk} {lj} {km}

hypB _ _ ([9a] {jk = jk} {lm} {mj}) = lemma-[9a] {jk = jk} {lm} {mj}
hypB _ _ ([9b] {jk = jk} {lm} {jm} {mk} {lj}) = lemma-[9b] {jk = jk} {lm} {jm} {mk} {lj}
hypB _ _ ([9c] {jk = jk} {lm} {jl} {mk}) = lemma-[9c] {jk = jk} {lm} {jl} {mk}
hypB _ _ ([10] {jk = jk}) = lemma-[10] {jk = jk}
hypB _ _ ([11] {kl = kl} {jk} {jl}) = lemma-[11] {kl = kl} {jk} {jl}
hypB _ _ ([12] {jl = jl} {kl} {jk}) = lemma-[12] {jl = jl} {kl} {jk}
hypB _ _ ([13] {kl = kl} {jk} {jl}) = lemma-[13] {kl = kl} {jk} {jl}
hypB _ _ ([14] {jl = jl} {kl} {jk}) = lemma-[14] {jl = jl} {kl} {jk}
hypB _ _ ([15] {jk = jk}) = lemma-[15] {jk = jk}
hypB _ _ ([16] {jk = jk}) = lemma-[16] {jk = jk}
hypB _ _ ([17] {jk = jk}) = lemma-[17] {jk = jk}
hypB _ _ ([18] {jk = jk}) = lemma-[18] {jk = jk}
hypB _ _ ([19a] {jk = jk} {lm} {jl} {km} {kl}) = lemma-[19a] {jk = jk} {lm} {jl} {km} {kl}

completeness : completeness-property
completeness {w} {v} = reidemeister-schreier-simplified f g hypA hypB w v
