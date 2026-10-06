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
-- loses sharing: it exhausts a 3 GB heap, where the default
-- call-by-need checks this module in under 10 minutes and 500 MB.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_; auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open Monoid-Equational
open import Presentation.Tactics.Words

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)
open TwoLevel-Less
open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified ; f ; g)
open TwoLevel-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Simplified-Lemmas
open BCu

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax19a where

  lemma-[19a] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} {jl : Less j l} {km : Less k m} {kl : Less k l} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (K jk • K lm • K jl • K km) === (g ʷ) (K jl • K km • K jk • K lm)

  lemma-[19a] {jk = ₀₁} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₀₁} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₀₁} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₀₁} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₀₁} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₀₁} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₀₁} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₀₁} {₁₂} {₀₁} {₁₂} {()}
  lemma-[19a] {jk = ₀₁} {₁₃} {₀₁} {₁₃} {()}
  lemma-[19a] {jk = ₀₁} {₁₄} {₀₁} {₁₄} {()}
  lemma-[19a] {jk = ₀₁} {₁₅} {₀₁} {₁₅} {()}
  lemma-[19a] {jk = ₀₁} {₁₆} {₀₁} {₁₆} {()}
  lemma-[19a] {jk = ₀₁} {₁₇} {₀₁} {₁₇} {()}
  lemma-[19a] {jk = ₀₁} {₂₃} {₀₂} {₁₃} {₁₂} = symm (axiom [S15])
  lemma-[19a] {jk = ₀₁} {₂₄} {₀₂} {₁₄} {₁₂} = by-basis-change (X₃₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₂₅} {₀₂} {₁₅} {₁₂} = by-basis-change (X₃₅) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₂₆} {₀₂} {₁₆} {₁₂} = by-basis-change (X₃₆) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₂₇} {₀₂} {₁₇} {₁₂} = by-basis-change (X₃₇) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₃₄} {₀₃} {₁₄} {₁₃} = by-basis-change (X₃₄ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₃₅} {₀₃} {₁₅} {₁₃} = by-basis-change (X₃₅ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₃₆} {₀₃} {₁₆} {₁₃} = by-basis-change (X₃₆ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₃₇} {₀₃} {₁₇} {₁₃} = by-basis-change (X₃₇ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₄₅} {₀₄} {₁₅} {₁₄} = by-basis-change (X₃₅ • X₂₃ • X₃₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₄₆} {₀₄} {₁₆} {₁₄} = by-basis-change (X₃₆ • X₂₃ • X₃₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₄₇} {₀₄} {₁₇} {₁₄} = by-basis-change (X₃₇ • X₂₃ • X₃₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₅₆} {₀₅} {₁₆} {₁₅} = by-basis-change (X₃₆ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₅₇} {₀₅} {₁₇} {₁₅} = by-basis-change (X₃₇ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₁} {₆₇} {₀₆} {₁₇} {₁₆} = by-basis-change (X₃₇ • X₂₃ • X₃₄ • X₄₅ • X₅₆) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₀₂} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₀₂} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₀₂} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₀₂} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₀₂} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₀₂} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₀₂} {₁₂} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₂} {₁₃} {₀₁} {₂₃} {()}
  lemma-[19a] {jk = ₀₂} {₁₄} {₀₁} {₂₄} {()}
  lemma-[19a] {jk = ₀₂} {₁₅} {₀₁} {₂₅} {()}
  lemma-[19a] {jk = ₀₂} {₁₆} {₀₁} {₂₆} {()}
  lemma-[19a] {jk = ₀₂} {₁₇} {₀₁} {₂₇} {()}
  lemma-[19a] {jk = ₀₂} {₂₃} {₀₂} {₂₃} {()}
  lemma-[19a] {jk = ₀₂} {₂₄} {₀₂} {₂₄} {()}
  lemma-[19a] {jk = ₀₂} {₂₅} {₀₂} {₂₅} {()}
  lemma-[19a] {jk = ₀₂} {₂₆} {₀₂} {₂₆} {()}
  lemma-[19a] {jk = ₀₂} {₂₇} {₀₂} {₂₇} {()}
  lemma-[19a] {jk = ₀₂} {₃₄} {₀₃} {₂₄} {₂₃} = by-basis-change (X₃₄ • X₂₃ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₃₅} {₀₃} {₂₅} {₂₃} = by-basis-change (X₃₅ • X₂₃ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₃₆} {₀₃} {₂₆} {₂₃} = by-basis-change (X₃₆ • X₂₃ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₃₇} {₀₃} {₂₇} {₂₃} = by-basis-change (X₃₇ • X₂₃ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₄₅} {₀₄} {₂₅} {₂₄} = by-basis-change (X₃₅ • X₂₄ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₄₆} {₀₄} {₂₆} {₂₄} = by-basis-change (X₃₆ • X₂₄ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₄₇} {₀₄} {₂₇} {₂₄} = by-basis-change (X₃₇ • X₂₄ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₅₆} {₀₅} {₂₆} {₂₅} = by-basis-change (X₃₆ • X₂₅ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₅₇} {₀₅} {₂₇} {₂₅} = by-basis-change (X₃₇ • X₂₅ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₂} {₆₇} {₀₆} {₂₇} {₂₆} = by-basis-change (X₃₇ • X₂₆ • X₁₂) (symm (axiom [S15])) 100 auto


  lemma-[19a] {jk = ₀₃} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₀₃} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₀₃} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₀₃} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₀₃} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₀₃} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₀₃} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₀₃} {₁₂} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₃} {₁₃} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₃} {₁₄} {₀₁} {₃₄} {()}
  lemma-[19a] {jk = ₀₃} {₁₅} {₀₁} {₃₅} {()}
  lemma-[19a] {jk = ₀₃} {₁₆} {₀₁} {₃₆} {()}
  lemma-[19a] {jk = ₀₃} {₁₇} {₀₁} {₃₇} {()}
  lemma-[19a] {jk = ₀₃} {₂₃} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₃} {₂₄} {₀₂} {₃₄} {()}
  lemma-[19a] {jk = ₀₃} {₂₅} {₀₂} {₃₅} {()}
  lemma-[19a] {jk = ₀₃} {₂₆} {₀₂} {₃₆} {()}
  lemma-[19a] {jk = ₀₃} {₂₇} {₀₂} {₃₇} {()}
  lemma-[19a] {jk = ₀₃} {₃₄} {₀₃} {₃₄} {()}
  lemma-[19a] {jk = ₀₃} {₃₅} {₀₃} {₃₅} {()}
  lemma-[19a] {jk = ₀₃} {₃₆} {₀₃} {₃₆} {()}
  lemma-[19a] {jk = ₀₃} {₃₇} {₀₃} {₃₇} {()}
  lemma-[19a] {jk = ₀₃} {₄₅} {₀₄} {₃₅} {₃₄} = by-basis-change (X₃₅ • X₂₄ • X₁₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₃} {₄₆} {₀₄} {₃₆} {₃₄} = by-basis-change (X₃₆ • X₂₄ • X₁₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₃} {₄₇} {₀₄} {₃₇} {₃₄} = by-basis-change (X₃₇ • X₂₄ • X₁₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₃} {₅₆} {₀₅} {₃₆} {₃₅} = by-basis-change (X₃₆ • X₂₅ • X₁₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₃} {₅₇} {₀₅} {₃₇} {₃₅} = by-basis-change (X₃₇ • X₂₅ • X₁₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₃} {₆₇} {₀₆} {₃₇} {₃₆} = by-basis-change (X₃₇ • X₂₆ • X₁₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₄} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₀₄} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₀₄} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₀₄} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₀₄} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₀₄} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₀₄} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₀₄} {₁₂} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₄} {₁₃} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₄} {₁₄} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₄} {₁₅} {₀₁} {₄₅} {()}
  lemma-[19a] {jk = ₀₄} {₁₆} {₀₁} {₄₆} {()}
  lemma-[19a] {jk = ₀₄} {₁₇} {₀₁} {₄₇} {()}
  lemma-[19a] {jk = ₀₄} {₂₃} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₄} {₂₄} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₄} {₂₅} {₀₂} {₄₅} {()}
  lemma-[19a] {jk = ₀₄} {₂₆} {₀₂} {₄₆} {()}
  lemma-[19a] {jk = ₀₄} {₂₇} {₀₂} {₄₇} {()}
  lemma-[19a] {jk = ₀₄} {₃₄} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₄} {₃₅} {₀₃} {₄₅} {()}
  lemma-[19a] {jk = ₀₄} {₃₆} {₀₃} {₄₆} {()}
  lemma-[19a] {jk = ₀₄} {₃₇} {₀₃} {₄₇} {()}
  lemma-[19a] {jk = ₀₄} {₄₅} {₀₄} {₄₅} {()}
  lemma-[19a] {jk = ₀₄} {₄₆} {₀₄} {₄₆} {()}
  lemma-[19a] {jk = ₀₄} {₄₇} {₀₄} {₄₇} {()}
  lemma-[19a] {jk = ₀₄} {₅₆} {₀₅} {₄₆} {₄₅} = by-basis-change (X₃₆ • X₂₅ • X₁₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₄} {₅₇} {₀₅} {₄₇} {₄₅} = by-basis-change (X₃₇ • X₂₅ • X₁₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₄} {₆₇} {₀₆} {₄₇} {₄₆} = by-basis-change (X₃₇ • X₂₆ • X₁₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₅} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₀₅} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₀₅} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₀₅} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₀₅} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₀₅} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₀₅} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₀₅} {₁₂} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₁₃} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₁₄} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₁₅} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₁₆} {₀₁} {₅₆} {()}
  lemma-[19a] {jk = ₀₅} {₁₇} {₀₁} {₅₇} {()}
  lemma-[19a] {jk = ₀₅} {₂₃} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₂₄} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₂₅} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₂₆} {₀₂} {₅₆} {()}
  lemma-[19a] {jk = ₀₅} {₂₇} {₀₂} {₅₇} {()}
  lemma-[19a] {jk = ₀₅} {₃₄} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₃₅} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₃₆} {₀₃} {₅₆} {()}
  lemma-[19a] {jk = ₀₅} {₃₇} {₀₃} {₅₇} {()}
  lemma-[19a] {jk = ₀₅} {₄₅} {₀₄} {()} {kl}
  lemma-[19a] {jk = ₀₅} {₄₆} {₀₄} {₅₆} {()}
  lemma-[19a] {jk = ₀₅} {₄₇} {₀₄} {₅₇} {()}
  lemma-[19a] {jk = ₀₅} {₅₆} {₀₅} {₅₆} {()}
  lemma-[19a] {jk = ₀₅} {₅₇} {₀₅} {₅₇} {()}
  lemma-[19a] {jk = ₀₅} {₆₇} {₀₆} {₅₇} {₅₆} = by-basis-change (X₃₇ • X₂₆ • X₁₅) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₀₆} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₀₆} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₀₆} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₀₆} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₀₆} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₀₆} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₀₆} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₀₆} {₁₂} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₁₃} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₁₄} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₁₅} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₁₆} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₁₇} {₀₁} {₆₇} {()}
  lemma-[19a] {jk = ₀₆} {₂₃} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₂₄} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₂₅} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₂₆} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₂₇} {₀₂} {₆₇} {()}
  lemma-[19a] {jk = ₀₆} {₃₄} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₃₅} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₃₆} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₃₇} {₀₃} {₆₇} {()}
  lemma-[19a] {jk = ₀₆} {₄₅} {₀₄} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₄₆} {₀₄} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₄₇} {₀₄} {₆₇} {()}
  lemma-[19a] {jk = ₀₆} {₅₆} {₀₅} {()} {kl}
  lemma-[19a] {jk = ₀₆} {₅₇} {₀₅} {₆₇} {()}
  lemma-[19a] {jk = ₀₆} {₆₇} {₀₆} {₆₇} {()}
  lemma-[19a] {jk = ₀₇} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₀₇} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₀₇} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₀₇} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₀₇} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₀₇} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₀₇} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₀₇} {₁₂} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₁₃} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₁₄} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₁₅} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₁₆} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₁₇} {₀₁} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₂₃} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₂₄} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₂₅} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₂₆} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₂₇} {₀₂} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₃₄} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₃₅} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₃₆} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₃₇} {₀₃} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₄₅} {₀₄} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₄₆} {₀₄} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₄₇} {₀₄} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₅₆} {₀₅} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₅₇} {₀₅} {()} {kl}
  lemma-[19a] {jk = ₀₇} {₆₇} {₀₆} {()} {kl}
  lemma-[19a] {jk = ₁₂} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₂} {₂₃} {₁₂} {₂₃} {()}
  lemma-[19a] {jk = ₁₂} {₂₄} {₁₂} {₂₄} {()}
  lemma-[19a] {jk = ₁₂} {₂₅} {₁₂} {₂₅} {()}
  lemma-[19a] {jk = ₁₂} {₂₆} {₁₂} {₂₆} {()}
  lemma-[19a] {jk = ₁₂} {₂₇} {₁₂} {₂₇} {()}
  lemma-[19a] {jk = ₁₂} {₃₄} {₁₃} {₂₄} {₂₃} = by-basis-change (X₃₄ • X₂₃ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₃₅} {₁₃} {₂₅} {₂₃} = by-basis-change (X₃₅ • X₂₃ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₃₆} {₁₃} {₂₆} {₂₃} = by-basis-change (X₃₆ • X₂₃ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₃₇} {₁₃} {₂₇} {₂₃} = by-basis-change (X₃₇ • X₂₃ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₄₅} {₁₄} {₂₅} {₂₄} = by-basis-change (X₃₅ • X₂₄ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₄₆} {₁₄} {₂₆} {₂₄} = by-basis-change (X₃₆ • X₂₄ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₄₇} {₁₄} {₂₇} {₂₄} = by-basis-change (X₃₇ • X₂₄ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₅₆} {₁₅} {₂₆} {₂₅} = by-basis-change (X₃₆ • X₂₅ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₅₇} {₁₅} {₂₇} {₂₅} = by-basis-change (X₃₇ • X₂₅ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₂} {₆₇} {₁₆} {₂₇} {₂₆} = by-basis-change (X₃₇ • X₂₆ • X₁₂ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₃} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₃} {₂₃} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₃} {₂₄} {₁₂} {₃₄} {()}
  lemma-[19a] {jk = ₁₃} {₂₅} {₁₂} {₃₅} {()}
  lemma-[19a] {jk = ₁₃} {₂₆} {₁₂} {₃₆} {()}
  lemma-[19a] {jk = ₁₃} {₂₇} {₁₂} {₃₇} {()}
  lemma-[19a] {jk = ₁₃} {₃₄} {₁₃} {₃₄} {()}
  lemma-[19a] {jk = ₁₃} {₃₅} {₁₃} {₃₅} {()}
  lemma-[19a] {jk = ₁₃} {₃₆} {₁₃} {₃₆} {()}
  lemma-[19a] {jk = ₁₃} {₃₇} {₁₃} {₃₇} {()}
  lemma-[19a] {jk = ₁₃} {₄₅} {₁₄} {₃₅} {₃₄} = by-basis-change (X₃₅ • X₂₄ • X₁₃ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₃} {₄₆} {₁₄} {₃₆} {₃₄} = by-basis-change (X₃₆ • X₂₄ • X₁₃ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₃} {₄₇} {₁₄} {₃₇} {₃₄} = by-basis-change (X₃₇ • X₂₄ • X₁₃ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₃} {₅₆} {₁₅} {₃₆} {₃₅} = by-basis-change (X₃₆ • X₂₅ • X₁₃ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₃} {₅₇} {₁₅} {₃₇} {₃₅} = by-basis-change (X₃₇ • X₂₅ • X₁₃ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₃} {₆₇} {₁₆} {₃₇} {₃₆} = by-basis-change (X₃₇ • X₂₆ • X₁₃ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₄} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₄} {₂₃} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₄} {₂₄} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₄} {₂₅} {₁₂} {₄₅} {()}
  lemma-[19a] {jk = ₁₄} {₂₆} {₁₂} {₄₆} {()}
  lemma-[19a] {jk = ₁₄} {₂₇} {₁₂} {₄₇} {()}
  lemma-[19a] {jk = ₁₄} {₃₄} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₄} {₃₅} {₁₃} {₄₅} {()}
  lemma-[19a] {jk = ₁₄} {₃₆} {₁₃} {₄₆} {()}
  lemma-[19a] {jk = ₁₄} {₃₇} {₁₃} {₄₇} {()}
  lemma-[19a] {jk = ₁₄} {₄₅} {₁₄} {₄₅} {()}
  lemma-[19a] {jk = ₁₄} {₄₆} {₁₄} {₄₆} {()}
  lemma-[19a] {jk = ₁₄} {₄₇} {₁₄} {₄₇} {()}
  lemma-[19a] {jk = ₁₄} {₅₆} {₁₅} {₄₆} {₄₅} = by-basis-change (X₃₆ • X₂₅ • X₁₄ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₄} {₅₇} {₁₅} {₄₇} {₄₅} = by-basis-change (X₃₇ • X₂₅ • X₁₄ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₄} {₆₇} {₁₆} {₄₇} {₄₆} = by-basis-change (X₃₇ • X₂₆ • X₁₄ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₅} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₅} {₂₃} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₅} {₂₄} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₅} {₂₅} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₅} {₂₆} {₁₂} {₅₆} {()}
  lemma-[19a] {jk = ₁₅} {₂₇} {₁₂} {₅₇} {()}
  lemma-[19a] {jk = ₁₅} {₃₄} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₅} {₃₅} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₅} {₃₆} {₁₃} {₅₆} {()}
  lemma-[19a] {jk = ₁₅} {₃₇} {₁₃} {₅₇} {()}
  lemma-[19a] {jk = ₁₅} {₄₅} {₁₄} {()} {kl}
  lemma-[19a] {jk = ₁₅} {₄₆} {₁₄} {₅₆} {()}
  lemma-[19a] {jk = ₁₅} {₄₇} {₁₄} {₅₇} {()}
  lemma-[19a] {jk = ₁₅} {₅₆} {₁₅} {₅₆} {()}
  lemma-[19a] {jk = ₁₅} {₅₇} {₁₅} {₅₇} {()}
  lemma-[19a] {jk = ₁₅} {₆₇} {₁₆} {₅₇} {₅₆} = by-basis-change (X₃₇ • X₂₆ • X₁₅ • X₀₁) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₁₆} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₆} {₂₃} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₂₄} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₂₅} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₂₆} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₂₇} {₁₂} {₆₇} {()}
  lemma-[19a] {jk = ₁₆} {₃₄} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₃₅} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₃₆} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₃₇} {₁₃} {₆₇} {()}
  lemma-[19a] {jk = ₁₆} {₄₅} {₁₄} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₄₆} {₁₄} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₄₇} {₁₄} {₆₇} {()}
  lemma-[19a] {jk = ₁₆} {₅₆} {₁₅} {()} {kl}
  lemma-[19a] {jk = ₁₆} {₅₇} {₁₅} {₆₇} {()}
  lemma-[19a] {jk = ₁₆} {₆₇} {₁₆} {₆₇} {()}
  lemma-[19a] {jk = ₁₇} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₁₇} {₂₃} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₂₄} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₂₅} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₂₆} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₂₇} {₁₂} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₃₄} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₃₅} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₃₆} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₃₇} {₁₃} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₄₅} {₁₄} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₄₆} {₁₄} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₄₇} {₁₄} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₅₆} {₁₅} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₅₇} {₁₅} {()} {kl}
  lemma-[19a] {jk = ₁₇} {₆₇} {₁₆} {()} {kl}
  lemma-[19a] {jk = ₂₃} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₃} {₃₄} {₂₃} {₃₄} {()}
  lemma-[19a] {jk = ₂₃} {₃₅} {₂₃} {₃₅} {()}
  lemma-[19a] {jk = ₂₃} {₃₆} {₂₃} {₃₆} {()}
  lemma-[19a] {jk = ₂₃} {₃₇} {₂₃} {₃₇} {()}
  lemma-[19a] {jk = ₂₃} {₄₅} {₂₄} {₃₅} {₃₄} = by-basis-change (X₃₅ • X₂₄ • X₁₃ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₃} {₄₆} {₂₄} {₃₆} {₃₄} = by-basis-change (X₃₆ • X₂₄ • X₁₃ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₃} {₄₇} {₂₄} {₃₇} {₃₄} = by-basis-change (X₃₇ • X₂₄ • X₁₃ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₃} {₅₆} {₂₅} {₃₆} {₃₅} = by-basis-change (X₃₆ • X₂₅ • X₁₃ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₃} {₅₇} {₂₅} {₃₇} {₃₅} = by-basis-change (X₃₇ • X₂₅ • X₁₃ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₃} {₆₇} {₂₆} {₃₇} {₃₆} = by-basis-change (X₃₇ • X₂₆ • X₁₃ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₄} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₄} {₃₄} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₄} {₃₅} {₂₃} {₄₅} {()}
  lemma-[19a] {jk = ₂₄} {₃₆} {₂₃} {₄₆} {()}
  lemma-[19a] {jk = ₂₄} {₃₇} {₂₃} {₄₇} {()}
  lemma-[19a] {jk = ₂₄} {₄₅} {₂₄} {₄₅} {()}
  lemma-[19a] {jk = ₂₄} {₄₆} {₂₄} {₄₆} {()}
  lemma-[19a] {jk = ₂₄} {₄₇} {₂₄} {₄₇} {()}
  lemma-[19a] {jk = ₂₄} {₅₆} {₂₅} {₄₆} {₄₅} = by-basis-change (X₃₆ • X₂₅ • X₁₄ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₄} {₅₇} {₂₅} {₄₇} {₄₅} = by-basis-change (X₃₇ • X₂₅ • X₁₄ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₄} {₆₇} {₂₆} {₄₇} {₄₆} = by-basis-change (X₃₇ • X₂₆ • X₁₄ • X₀₁ • X₁₂) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₅} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₅} {₃₄} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₅} {₃₅} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₅} {₃₆} {₂₃} {₅₆} {()}
  lemma-[19a] {jk = ₂₅} {₃₇} {₂₃} {₅₇} {()}
  lemma-[19a] {jk = ₂₅} {₄₅} {₂₄} {()} {kl}
  lemma-[19a] {jk = ₂₅} {₄₆} {₂₄} {₅₆} {()}
  lemma-[19a] {jk = ₂₅} {₄₇} {₂₄} {₅₇} {()}
  lemma-[19a] {jk = ₂₅} {₅₆} {₂₅} {₅₆} {()}
  lemma-[19a] {jk = ₂₅} {₅₇} {₂₅} {₅₇} {()}
  lemma-[19a] {jk = ₂₅} {₆₇} {₂₆} {₅₇} {₅₆} = by-basis-change (X₃₇ • X₂₆ • X₁₄ • X₀₁ • X₁₂ • X₄₅) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₂₆} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₆} {₃₄} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₆} {₃₅} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₆} {₃₆} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₆} {₃₇} {₂₃} {₆₇} {()}
  lemma-[19a] {jk = ₂₆} {₄₅} {₂₄} {()} {kl}
  lemma-[19a] {jk = ₂₆} {₄₆} {₂₄} {()} {kl}
  lemma-[19a] {jk = ₂₆} {₄₇} {₂₄} {₆₇} {()}
  lemma-[19a] {jk = ₂₆} {₅₆} {₂₅} {()} {kl}
  lemma-[19a] {jk = ₂₆} {₅₇} {₂₅} {₆₇} {()}
  lemma-[19a] {jk = ₂₆} {₆₇} {₂₆} {₆₇} {()}
  lemma-[19a] {jk = ₂₇} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₂₇} {₃₄} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₃₅} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₃₆} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₃₇} {₂₃} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₄₅} {₂₄} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₄₆} {₂₄} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₄₇} {₂₄} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₅₆} {₂₅} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₅₇} {₂₅} {()} {kl}
  lemma-[19a] {jk = ₂₇} {₆₇} {₂₆} {()} {kl}
  lemma-[19a] {jk = ₃₄} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₄} {₄₅} {₃₄} {₄₅} {()}
  lemma-[19a] {jk = ₃₄} {₄₆} {₃₄} {₄₆} {()}
  lemma-[19a] {jk = ₃₄} {₄₇} {₃₄} {₄₇} {()}
  lemma-[19a] {jk = ₃₄} {₅₆} {₃₅} {₄₆} {₄₅} = by-basis-change (X₃₆ • X₂₅ • X₁₄ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₃₄} {₅₇} {₃₅} {₄₇} {₄₅} = by-basis-change (X₃₇ • X₂₅ • X₁₄ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₃₄} {₆₇} {₃₆} {₄₇} {₄₆} = by-basis-change (X₃₇ • X₂₆ • X₁₄ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₃₅} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₅} {₄₅} {₃₄} {()} {kl}
  lemma-[19a] {jk = ₃₅} {₄₆} {₃₄} {₅₆} {()}
  lemma-[19a] {jk = ₃₅} {₄₇} {₃₄} {₅₇} {()}
  lemma-[19a] {jk = ₃₅} {₅₆} {₃₅} {₅₆} {()}
  lemma-[19a] {jk = ₃₅} {₅₇} {₃₅} {₅₇} {()}
  lemma-[19a] {jk = ₃₅} {₆₇} {₃₆} {₅₇} {₅₆} = by-basis-change (X₃₇ • X₂₆ • X₁₅ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₃₆} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₆} {₄₅} {₃₄} {()} {kl}
  lemma-[19a] {jk = ₃₆} {₄₆} {₃₄} {()} {kl}
  lemma-[19a] {jk = ₃₆} {₄₇} {₃₄} {₆₇} {()}
  lemma-[19a] {jk = ₃₆} {₅₆} {₃₅} {()} {kl}
  lemma-[19a] {jk = ₃₆} {₅₇} {₃₅} {₆₇} {()}
  lemma-[19a] {jk = ₃₆} {₆₇} {₃₆} {₆₇} {()}
  lemma-[19a] {jk = ₃₇} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₃₇} {₄₅} {₃₄} {()} {kl}
  lemma-[19a] {jk = ₃₇} {₄₆} {₃₄} {()} {kl}
  lemma-[19a] {jk = ₃₇} {₄₇} {₃₄} {()} {kl}
  lemma-[19a] {jk = ₃₇} {₅₆} {₃₅} {()} {kl}
  lemma-[19a] {jk = ₃₇} {₅₇} {₃₅} {()} {kl}
  lemma-[19a] {jk = ₃₇} {₆₇} {₃₆} {()} {kl}
  lemma-[19a] {jk = ₄₅} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₄₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₄₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₄₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₅} {₅₆} {₄₅} {₅₆} {()}
  lemma-[19a] {jk = ₄₅} {₅₇} {₄₅} {₅₇} {()}
  lemma-[19a] {jk = ₄₅} {₆₇} {₄₆} {₅₇} {₅₆} = by-basis-change (X₃₇ • X₂₆ • X₁₅ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S15])) 100 auto
  lemma-[19a] {jk = ₄₆} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₄₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₄₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₄₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₆} {₅₆} {₄₅} {()} {kl}
  lemma-[19a] {jk = ₄₆} {₅₇} {₄₅} {₆₇} {()}
  lemma-[19a] {jk = ₄₆} {₆₇} {₄₆} {₆₇} {()}
  lemma-[19a] {jk = ₄₇} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₄₅} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₄₆} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₄₇} {()} {km} {kl}
  lemma-[19a] {jk = ₄₇} {₅₆} {₄₅} {()} {kl}
  lemma-[19a] {jk = ₄₇} {₅₇} {₄₅} {()} {kl}
  lemma-[19a] {jk = ₄₇} {₆₇} {₄₆} {()} {kl}
  lemma-[19a] {jk = ₅₆} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₄₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₄₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₄₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₅₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₅₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₆} {₆₇} {₅₆} {₆₇} {()}
  lemma-[19a] {jk = ₅₇} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₄₅} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₄₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₄₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₅₆} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₅₇} {()} {km} {kl}
  lemma-[19a] {jk = ₅₇} {₆₇} {₅₆} {()} {kl}
  lemma-[19a] {jk = ₆₇} {₀₁} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₀₂} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₀₃} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₀₄} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₀₅} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₀₆} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₀₇} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₁₂} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₁₃} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₁₄} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₁₅} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₁₆} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₁₇} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₂₃} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₂₄} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₂₅} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₂₆} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₂₇} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₃₄} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₃₅} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₃₆} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₃₇} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₄₅} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₄₆} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₄₇} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₅₆} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₅₇} {()} {km} {kl}
  lemma-[19a] {jk = ₆₇} {₆₇} {()} {km} {kl}
