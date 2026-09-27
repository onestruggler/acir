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
open TwoLevel
open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less ; f)
open TwoLevel-Less

module Examples.Groups.Clifford+CS-3qubit.Step1.Soundness where

  soundness-base : ∀ {w v} -> w === v ∈ TwoLevel-Less.Rel -> TwoLevel.Rel ⊢ (f ʷ) w === (f ʷ) v
  soundness-base [1] = axiom [1]
  soundness-base [2] = axiom [2]
  soundness-base [3] = axiom [3]
  soundness-base ([4] {jk = jk}) = axiom ([4] {jk = f<s jk})
  soundness-base ([5a] {kl = kl} {jk}) = axiom ([5] {kl = kl} {jk = f<s jk} {jl = f<s (transitivity jk kl)})
  soundness-base ([5b] {kl = kl} {lj}) = axiom ([5] {kl = kl} {jk = f>s (transitivity kl lj)} {jl = f>s lj})
  soundness-base ([5c] {kl = kl} {kj} {jl}) = axiom ([5] {kl = kl} {jk = f>s kj} {jl = f<s jl})
  soundness-base ([6a] {kl = kl} {jk}) = axiom ([6] {kl = kl} {jk = f<s jk} {jl = f<s (transitivity jk kl)})
  soundness-base ([6b] {kl = kl} {lj}) = axiom ([6] {kl = kl} {jk = f>s (transitivity kl lj)} {jl = f>s lj})
  soundness-base ([6c] {kl = kl} {kj} {jl}) = axiom ([6] {kl = kl} {jk = f>s kj} {jl = f<s jl})
  soundness-base ([7a] {jk = jk} {lm} {mj}) = axiom ([7] {jk = jk} {lm = lm} {jl = f>s (transitivity lm mj)} {jm = f>s mj} {kl = f>s (transitivity lm (transitivity mj jk))} {km = f>s (transitivity mj jk)})
  soundness-base ([7b] {jk = jk} {lm} {jm} {mk} {lj}) = axiom ([7] {jk = jk} {lm = lm} {jl = f>s lj} {jm = f<s jm} {kl = f>s (transitivity lj jk)} {km = f>s mk})
  soundness-base ([7c] {jk = jk} {lm} {jl} {mk}) = axiom ([7] {jk = jk} {lm = lm} {jl = f<s jl} {jm = f<s (transitivity jl lm)} {kl = f>s (transitivity lm mk)} {km = f>s mk})
  soundness-base ([8a] {jk = jk} {lm} {mj}) = axiom ([8] {jk = jk} {lm = lm} {jl = f>s (transitivity lm mj)} {jm = f>s mj} {kl = f>s (transitivity lm (transitivity mj jk))} {km = f>s (transitivity mj jk)})
  soundness-base ([8b] {jk = jk} {lm} {jm} {mk} {lj}) = axiom ([8] {jk = jk} {lm = lm} {jl = f>s lj} {jm = f<s jm} {kl = f>s (transitivity lj jk)} {km = f>s mk})
  soundness-base ([8c] {jk = jk} {lm} {jl} {mk}) = axiom ([8] {jk = jk} {lm = lm} {jl = f<s jl} {jm = f<s (transitivity jl lm)} {kl = f>s (transitivity lm mk)} {km = f>s mk})
  soundness-base ([8d] {jk = jk} {lm} {jl} {lk} {km}) = axiom ([8] {jk = jk} {lm = lm} {jl = f<s jl} {jm = f<s (transitivity jl lm)} {kl = f>s lk} {km = f<s km})
  soundness-base ([8e] {jk = jk} {lm} {kl}) = axiom ([8] {jk = jk} {lm = lm} {jl = f<s (transitivity jk kl)} {jm = f<s (transitivity (transitivity jk kl) lm) } {kl = f<s kl} {km = f<s (transitivity kl lm)})
  soundness-base ([8f] {jk = jk} {lm} {lj} {km}) = axiom ([8] {jk = jk} {lm = lm} {jl = f>s lj} {jm = f<s (transitivity jk km)} {kl = f>s (transitivity lj jk)} {km = f<s km})
  soundness-base ([9a] {jk = jk} {lm} {mj}) = axiom ([9] {jk = jk} {lm = lm} {jl = f>s (transitivity lm mj)} {jm = f>s mj} {kl = f>s (transitivity lm (transitivity mj jk))} {km = f>s (transitivity mj jk)})
  soundness-base ([9b] {jk = jk} {lm} {jm} {mk} {lj}) = axiom ([9] {jk = jk} {lm = lm} {jl = f>s lj} {jm = f<s jm} {kl = f>s (transitivity lj jk)} {km = f>s mk})
  soundness-base ([9c] {jk = jk} {lm} {jl} {mk}) = axiom ([9] {jk = jk} {lm = lm} {jl = f<s jl} {jm = f<s (transitivity jl lm)} {kl = f>s (transitivity lm mk)} {km = f>s mk})
  soundness-base ([10] {jk = jk}) = axiom ([10] {jk = jk})
  soundness-base ([11] {kl = kl} {jk} {jl}) = axiom ([11])
  soundness-base [12] = axiom [12]
  soundness-base [13] = axiom [13]
  soundness-base [14] = axiom [14]
  soundness-base [15] = axiom [15]
  soundness-base [16] = axiom [16]
  soundness-base [17] = axiom [17]
  soundness-base [18] = axiom [18]
  soundness-base ([19a] {jk = jk} {lm} {jl} {km} {kl}) = axiom ([19] {jk = jk} {lm} {jl} {km} {f<s kl})
  
  -- Proof of the soundness theorem: All the work was done in the base
  -- cases. The rest is just an obvious induction.
  soundness : ∀ {w v : Word TwoLevel-Less.Gen} -> TwoLevel-Less.Rel ⊢ w === v -> TwoLevel.Rel ⊢ (f ʷ) w === (f ʷ) v
  soundness (axiom x) = soundness-base x
  soundness refl = refl
  soundness (symm deriv) = symm (soundness deriv)
  soundness (trans deriv deriv₁) = trans (soundness deriv) (soundness deriv₁)
  soundness (cong deriv deriv₁) = cong (soundness deriv) (soundness deriv₁)
  soundness assoc = assoc
  soundness left-unit = left-unit
  soundness right-unit = right-unit
