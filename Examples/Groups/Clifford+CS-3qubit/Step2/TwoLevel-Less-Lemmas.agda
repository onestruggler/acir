------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (auto)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec ; yes ; no ; does)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≟_ ; _≤?_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Presentation.Tactics.Lists
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words
open Rewriting

open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)
open TwoLevel-Less
open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified)
open TwoLevel-Simplified hiding (Gen ; Rel)

module Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Less-Lemmas where

-- ----------------------------------------------------------------------
-- * Data required for applying monoid tactics to 2-level generators

module TwoLevel-Less-Data where

  open Monoid-Equational
  open Associative

  -- Convert an index to a natural number.
  nat-of-index : Index -> ℕ
  nat-of-index ₀ = 0
  nat-of-index ₁ = 1
  nat-of-index ₂ = 2
  nat-of-index ₃ = 3
  nat-of-index ₄ = 4
  nat-of-index ₅ = 5
  nat-of-index ₆ = 6
  nat-of-index ₇ = 7

  maybe-less : (j k : Index) -> Maybe (Less j k)
  maybe-less ₀ ₁ = just ₀₁
  maybe-less ₀ ₂ = just ₀₂
  maybe-less ₀ ₃ = just ₀₃
  maybe-less ₀ ₄ = just ₀₄
  maybe-less ₀ ₅ = just ₀₅
  maybe-less ₀ ₆ = just ₀₆
  maybe-less ₀ ₇ = just ₀₇
  maybe-less ₁ ₂ = just ₁₂
  maybe-less ₁ ₃ = just ₁₃
  maybe-less ₁ ₄ = just ₁₄
  maybe-less ₁ ₅ = just ₁₅
  maybe-less ₁ ₆ = just ₁₆
  maybe-less ₁ ₇ = just ₁₇
  maybe-less ₂ ₃ = just ₂₃
  maybe-less ₂ ₄ = just ₂₄
  maybe-less ₂ ₅ = just ₂₅
  maybe-less ₂ ₆ = just ₂₆
  maybe-less ₂ ₇ = just ₂₇
  maybe-less ₃ ₄ = just ₃₄
  maybe-less ₃ ₅ = just ₃₅
  maybe-less ₃ ₆ = just ₃₆
  maybe-less ₃ ₇ = just ₃₇
  maybe-less ₄ ₅ = just ₄₅
  maybe-less ₄ ₆ = just ₄₆
  maybe-less ₄ ₇ = just ₄₇
  maybe-less ₅ ₆ = just ₅₆
  maybe-less ₅ ₇ = just ₅₇
  maybe-less ₆ ₇ = just ₆₇
  maybe-less _ _ = nothing


  infix 8 _<?_

  _<?_ : (j k : Index) -> Maybe (Less j k)
  _<?_ = maybe-less
  
  -- Information on the commutativity of generators.
  comm : (x y : Gen) -> Maybe (commutes Rel x y)
  comm (i-gen x) (i-gen y) with x <? y | y <? x
  ... | just h | h2 = just (axiom ([4] {jk = h}))
  ... | nothing | just h2 = just (symm (axiom ([4] {jk = h2})))
  ... | nothing | nothing = nothing
  comm (i-gen x) (X-gen {j = j} {k = k} jk) with x <? j | k <? x
  ... | just h1 | h2 = just (axiom ([5a] {jk = h1}))
  ... | nothing | just h2 = just (axiom ([5b] {lj = h2}))
  ... | nothing | nothing with j <? x | x <? k
  ... | just jx | just xk = just (axiom ([5c] {kj = jx} {xk}))
  ... | _ | _ = nothing
  comm (i-gen x) (K-gen {j = j} {k = k} jk) with x <? j | k <? x
  ... | just h1 | h2 = just (axiom ([6a] {jk = h1}))
  ... | nothing | just h2 = just (axiom ([6b] {lj = h2}))
  ... | nothing | nothing with j <? x | x <? k
  ... | just jx | just xk = just (axiom ([6c] {kj = jx} {xk}))
  ... | _ | _ = nothing

  comm (X-gen {j = j} {k = k} jk) (i-gen x) with x <? j | k <? x
  ... | just h1 | h2 = just (symm (axiom ([5a] {jk = h1})))
  ... | nothing | just h2 = just (symm (axiom ([5b] {lj = h2})))
  ... | nothing | nothing with j <? x | x <? k
  ... | just jx | just xk = just (symm (axiom ([5c] {kj = jx} {xk})))
  ... | _ | _ = nothing

  comm (X-gen {j = j} {k = k} jk) (X-gen {j = l} {k = m} lm) with m <? j
  ... | just x = just (axiom ([7a] {mj = x}))
  ... | nothing with j <? m | m <? k | l <? j
  ... | just jm | just mk | just lj = just (axiom ([7b] {jm = jm} {mk} {lj}))
  ... | _ | _ | _ with j <? l | m <? k
  ... | just jl | just mk = just (axiom ([7c] {jl = jl} {mk}))
  ... | _ | _ with j <? l | k <? m | l <? k
  ... | just jl | just km | just lk = just (symm (axiom ([7b] {jm = lk} {km} {jl})))
  ... | _ | _ | _ with k <? l
  ... | just x = just (symm (axiom ([7a] {mj = x})))
  ... | nothing with l <? j | k <? m
  ... | just lj | just km = just (symm (axiom ([7c] {jl = lj} {km})))
  ... | h1 | h2 = nothing

  comm (X-gen {j = j} {k = k} jk) (K-gen {j = l} {k = m} lm) with m <? j
  ... | just x = just (axiom ([8a] {mj = x}))
  ... | nothing with j <? m | m <? k | l <? j
  ... | just jm | just mk | just lj = just (axiom ([8b] {jm = jm} {mk} {lj}))
  ... | _ | _ | _ with j <? l | m <? k
  ... | just jl | just mk = just (axiom ([8c] {jl = jl} {mk}))
  ... | _ | _ with j <? l | k <? m | l <? k
  ... | just jl | just km | just lk = just (axiom ([8d] {jl = jl} {lk} {km}))
  ... | _ | _ | _ with k <? l
  ... | just x = just (axiom ([8e] {kl = x}))
  ... | nothing with l <? j | k <? m
  ... | just lj | just km = just (axiom ([8f] {lj = lj} {km}))
  ... | h1 | h2 = nothing

  comm (K-gen {j = l} {k = m} lm) (X-gen {j = j} {k = k} jk) with m <? j
  ... | just x = just (symm (axiom ([8a] {mj = x})))
  ... | nothing with j <? m | m <? k | l <? j
  ... | just jm | just mk | just lj = just (symm (axiom ([8b] {jm = jm} {mk} {lj})))
  ... | _ | _ | _ with j <? l | m <? k
  ... | just jl | just mk = just (symm (axiom ([8c] {jl = jl} {mk})))
  ... | _ | _ with j <? l | k <? m | l <? k
  ... | just jl | just km | just lk = just (symm (axiom ([8d] {jl = jl} {lk} {km})))
  ... | _ | _ | _ with k <? l
  ... | just x = just (symm (axiom ([8e] {kl = x})))
  ... | nothing with l <? j | k <? m
  ... | just lj | just km = just (symm (axiom ([8f] {lj = lj} {km})))
  ... | h1 | h2 = nothing

  comm (K-gen {j = j} {k = k} jk) (i-gen x) with x <? j | k <? x
  ... | just h1 | h2 = just (symm (axiom ([6a] {jk = h1})))
  ... | nothing | just h2 = just (symm (axiom ([6b] {lj = h2})))
  ... | nothing | nothing with j <? x | x <? k
  ... | just jx | just xk = just (symm (axiom ([6c] {kj = jx} {xk})))
  ... | _ | _ = nothing
  

  comm (K-gen {j = j} {k = k} jk) (K-gen {j = l} {k = m} lm) with m <? j
  ... | just x = just (axiom ([9a] {mj = x}))
  ... | nothing with j <? m | m <? k | l <? j
  ... | just jm | just mk | just lj = just (axiom ([9b] {jm = jm} {mk} {lj}))
  ... | _ | _ | _ with j <? l | m <? k
  ... | just jl | just mk = just (axiom ([9c] {jl = jl} {mk}))
  ... | _ | _ with j <? l | k <? m | l <? k
  ... | just jl | just km | just lk = just (symm (axiom ([9b] {jm = lk} {km} {jl})))
  ... | _ | _ | _ with k <? l
  ... | just x = just (symm (axiom ([9a] {mj = x})))
  ... | nothing with l <? j | k <? m
  ... | just lj | just km = just (symm (axiom ([9c] {jl = lj} {km})))
  ... | h1 | h2 = nothing

  -- We rank the generators to induce an order on them.
  rank : Gen -> ℕ
  rank (i-gen j) = 55 + (nat-of-index j)
  rank (X-gen {j} {k} jk) = 63 + (nat-of-index j) + 7 * (nat-of-index k)
  rank (K-gen {j} {k} jk) = (nat-of-index j) + 7 * (nat-of-index k)

  -- An ordering of the generators.
  less : Gen -> Gen -> Bool
  less g h = does (rank g ≤? rank h)

  -- Information about the inverses of the generators.
  group-like : Grouplike Rel
  group-like (i-gen j) = (i j ^ 3 , up-to-assoc auto (axiom ([1] {j})))
  group-like (X-gen jk) = (X jk , axiom [2])
  group-like (K-gen jk) = (K jk ^ 7 , up-to-assoc auto (axiom [3]))

-- Now we instantiate various modules with this information, to obtain
-- lemmas and tactics:

module Commuting-TwoLevel-Less = Commuting Gen Rel TwoLevel-Less-Data.comm TwoLevel-Less-Data.less
module Inverse-TwoLevel-Less = Inverse Gen Rel TwoLevel-Less-Data.group-like

-- ----------------------------------------------------------------------
-- * Rewrite rules for order of generators

module TwoLevel-Less-Step-Order where

  -- Here, we provide a rewrite rule for reducing powers of
  -- generators. This is helpful in defining the more general rewrite
  -- system below.

  open InContext
  open Associative  
  open Monoid-Equational
  open Commuting-TwoLevel-Less
  open Monoid-Lemmas

  -- K^2 = i ^ 3.
  lemma-K^2 : ∀ {j k} {jk : Less j k} -> Rel ⊢ K jk ^ 2 === i j ^ 3 • i k ^ 3
  lemma-K^2 {j} {k} {jk} =
    equational K jk ^ 2
      by (right-unit reversed)
    equals K jk ^ 2 • ε
      by (right axiom [1] reversed)
    equals K jk ^ 2 • i j ^ 4
      by (right-unit reversed)
    equals (K jk ^ 2 • i j ^ 4) • ε
      by (right axiom [1] reversed)
    equals (K jk ^ 2 • i j ^ 4) • i k ^ 4
      by general-assoc auto
    equals K jk ^ 2 • i j • (i j ^ 3 • i k) • i k ^ 3
      by (right right left lemma-comm-powers 3 1 (axiom ([4] {jk = jk})))
    equals K jk ^ 2 • i j • (i k • i j ^ 3) • i k ^ 3
      by general-assoc auto
    equals (K jk ^ 2 • i j • i k) • i j ^ 3 • i k ^ 3
      by (left axiom [18])
    equals ε • i j ^ 3 • i k ^ 3
      by left-unit
    equals i j ^ 3 • i k ^ 3

  -- Step function: Rewrite powers of generators modulo their order.
  step : Step-Function Gen Rel
  step (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ t) = just (t , at-head (axiom [1]))
  step (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ t) = just (t , at-head (axiom [1]))
  step (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ t) = just (t , at-head (axiom [1]))
  step (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t) = just (t , at-head (axiom [1]))
  step (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t) = just (t , at-head (axiom [1]))
  step (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t) = just (t , at-head (axiom [1]))
  step (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t) = just (t , at-head (axiom [1]))
  step (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t) = just (t , at-head (axiom [1]))
  
  step (K-gen ₀₁ ∷ K-gen ₀₁ ∷ t) = just (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ t , at-head (lemma-K^2))
  step (K-gen ₀₂ ∷ K-gen ₀₂ ∷ t) = just (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ t , at-head (lemma-K^2))
  step (K-gen ₀₃ ∷ K-gen ₀₃ ∷ t) = just (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head (lemma-K^2))
  step (K-gen ₀₄ ∷ K-gen ₀₄ ∷ t) = just (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-K^2))
  step (K-gen ₀₅ ∷ K-gen ₀₅ ∷ t) = just (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-K^2))
  step (K-gen ₀₆ ∷ K-gen ₀₆ ∷ t) = just (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-K^2))
  step (K-gen ₀₇ ∷ K-gen ₀₇ ∷ t) = just (i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-K^2))
  
  step (K-gen ₁₂ ∷ K-gen ₁₂ ∷ t) = just (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ t , at-head (lemma-K^2))
  step (K-gen ₁₃ ∷ K-gen ₁₃ ∷ t) = just (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head (lemma-K^2))
  step (K-gen ₁₄ ∷ K-gen ₁₄ ∷ t) = just (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-K^2))
  step (K-gen ₁₅ ∷ K-gen ₁₅ ∷ t) = just (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-K^2))
  step (K-gen ₁₆ ∷ K-gen ₁₆ ∷ t) = just (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-K^2))
  step (K-gen ₁₇ ∷ K-gen ₁₇ ∷ t) = just (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-K^2))
  step (K-gen ₂₃ ∷ K-gen ₂₃ ∷ t) = just (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head (lemma-K^2))
  step (K-gen ₂₄ ∷ K-gen ₂₄ ∷ t) = just (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-K^2))
  step (K-gen ₂₅ ∷ K-gen ₂₅ ∷ t) = just (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-K^2))
  step (K-gen ₂₆ ∷ K-gen ₂₆ ∷ t) = just (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-K^2))
  step (K-gen ₂₇ ∷ K-gen ₂₇ ∷ t) = just (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-K^2))
  step (K-gen ₃₄ ∷ K-gen ₃₄ ∷ t) = just (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-K^2))
  step (K-gen ₃₅ ∷ K-gen ₃₅ ∷ t) = just (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-K^2))
  step (K-gen ₃₆ ∷ K-gen ₃₆ ∷ t) = just (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-K^2))
  step (K-gen ₃₇ ∷ K-gen ₃₇ ∷ t) = just (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-K^2))
  step (K-gen ₄₅ ∷ K-gen ₄₅ ∷ t) = just (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-K^2))
  step (K-gen ₄₆ ∷ K-gen ₄₆ ∷ t) = just (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-K^2))
  step (K-gen ₄₇ ∷ K-gen ₄₇ ∷ t) = just (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-K^2))
  step (K-gen ₅₆ ∷ K-gen ₅₆ ∷ t) = just (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-K^2))
  step (K-gen ₅₇ ∷ K-gen ₅₇ ∷ t) = just (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-K^2))
  step (K-gen ₆₇ ∷ K-gen ₆₇ ∷ t) = just (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-K^2))


  step (X-gen ₀₁ ∷ X-gen ₀₁ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₀₂ ∷ X-gen ₀₂ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₀₃ ∷ X-gen ₀₃ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₀₄ ∷ X-gen ₀₄ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₀₅ ∷ X-gen ₀₅ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₀₆ ∷ X-gen ₀₆ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₀₇ ∷ X-gen ₀₇ ∷ t) = just (t , at-head (axiom [2]))

  step (X-gen ₁₂ ∷ X-gen ₁₂ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₁₃ ∷ X-gen ₁₃ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₁₄ ∷ X-gen ₁₄ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₁₅ ∷ X-gen ₁₅ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₁₆ ∷ X-gen ₁₆ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₁₇ ∷ X-gen ₁₇ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₂₃ ∷ X-gen ₂₃ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₂₄ ∷ X-gen ₂₄ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₂₅ ∷ X-gen ₂₅ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₂₆ ∷ X-gen ₂₆ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₂₇ ∷ X-gen ₂₇ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₃₄ ∷ X-gen ₃₄ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₃₅ ∷ X-gen ₃₅ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₃₆ ∷ X-gen ₃₆ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₃₇ ∷ X-gen ₃₇ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₄₅ ∷ X-gen ₄₅ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₄₆ ∷ X-gen ₄₆ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₄₇ ∷ X-gen ₄₇ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₅₆ ∷ X-gen ₅₆ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₅₇ ∷ X-gen ₅₇ ∷ t) = just (t , at-head (axiom [2]))
  step (X-gen ₆₇ ∷ X-gen ₆₇ ∷ t) = just (t , at-head (axiom [2]))

  step _ = nothing


module TwoLevel-Less-Rewrite-Order = Step-With-Standardization (step-cong TwoLevel-Less-Step-Order.step) Commuting-TwoLevel-Less.comm-canonical Commuting-TwoLevel-Less.lemma-comm-canonical renaming (general-rewrite to rewrite-order)


-- ----------------------------------------------------------------------
-- * A set of rewrite rules for 2-level operators

module TwoLevel-Less-Step where

  open Monoid-Equational
  open Monoid-Lemmas
  open Associative
  open InContext
  open TwoLevel-Less-Rewrite-Order 
  open TwoLevel-Less-Data hiding (comm)
  open TwoLevel-Less-Step-Order hiding (step)
  open Inverse-TwoLevel-Less  
  
  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- We prove various lemmas that are needed to justify the
  -- correctness of the rewrite relation below. Most of these lemmas
  -- have little intuitive value; they are basically just what is
  -- needed to make the rewriting work.

  -- K^7 = i K.
  lemma-K^7 : ∀ {j k} {jk : Less j k} -> Rel ⊢ K jk ^ 7 === K jk • i j • i k
  lemma-K^7 {j} {k} {jk} =
    equational K jk ^ 7
      by general-assoc auto
    equals K jk • K jk ^ 2 • K jk ^ 2 • K jk ^ 2
      by (right left lemma-K^2)
    equals K jk • (i j ^ 3 • i k ^ 3) • K jk ^ 2 • K jk ^ 2
      by (right right left lemma-K^2)
    equals K jk • (i j ^ 3 • i k ^ 3) • (i j ^ 3 • i k ^ 3) • K jk ^ 2
      by (right right right lemma-K^2)
    equals K jk • (i j ^ 3 • i k ^ 3) • (i j ^ 3 • i k ^ 3) • (i j ^ 3 • i k ^ 3)
      by general-assoc auto
    equals K jk • (i j ^ 3 • (i k ^ 3 • i j ^ 3) • i k ^ 3) • (i j ^ 3 • i k ^ 3)
      by (right left right left lemma-comm-powers 3 3 (axiom ([4] {jk = jk})) reversed)
    equals K jk • (i j ^ 3 • (i j ^ 3 • i k ^ 3) • i k ^ 3) • (i j ^ 3 • i k ^ 3)
      by general-assoc auto
    equals K jk • (i j ^ 4 • i j ^ 2) • (i k ^ 4 • i k ^ 2) • (i j ^ 3 • i k ^ 3)
      by (right left left axiom [1])
    equals K jk • (ε • i j ^ 2) • (i k ^ 4 • i k ^ 2) • (i j ^ 3 • i k ^ 3)
      by (right left left-unit)
    equals K jk • (i j ^ 2) • (i k ^ 4 • i k ^ 2) • (i j ^ 3 • i k ^ 3)
      by (right right left left axiom [1])
    equals K jk • (i j ^ 2) • (ε • i k ^ 2) • (i j ^ 3 • i k ^ 3)
      by (right right left left-unit)
    equals K jk • (i j ^ 2) • (i k ^ 2) • (i j ^ 3 • i k ^ 3)
      by (right right right lemma-comm-powers 3 3 (axiom ([4] {jk = jk})))
    equals K jk • (i j ^ 2) • (i k ^ 2) • (i k ^ 3 • i j ^ 3)
      by general-assoc auto
    equals K jk • (i j ^ 2) • (i k ^ 4 • i k ^ 1) • i j ^ 3
      by (right right left left axiom [1])
    equals K jk • (i j ^ 2) • (ε • i k ^ 1) • i j ^ 3
      by (right right left left-unit)
    equals K jk • (i j ^ 2) • (i k ^ 1) • i j ^ 3
      by (right right lemma-comm-powers 3 1 (axiom ([4] {jk = jk})) reversed)
    equals K jk • (i j ^ 2) • i j ^ 3 • (i k ^ 1)
      by general-assoc auto
    equals K jk • (i j ^ 4) • i j ^ 1 • (i k ^ 1)
      by (right left axiom [1])
    equals K jk • ε • i j ^ 1 • (i k ^ 1)
      by (right left-unit)
    equals K jk • i j • i k



  -- Another version of axiom [10].
  lemma-[10]' : ∀ {j k} {jk : Less j k} -> Rel ⊢ i j • X jk === X jk • i k
  lemma-[10]' {j} {k} {jk} =
    equational i j • X jk
      by trans (left axiom [2]) left-unit reversed
    equals (X jk • X jk) •  i j • X jk
      by general-assoc auto
    equals X jk • (X jk • i j) • X jk
      by (right left axiom [10] reversed)
    equals X jk • (i k • X jk) • X jk
      by general-assoc auto
    equals (X jk • i k) • (X jk • X jk)
      by trans (right axiom [2]) right-unit
    equals X jk • i k

  -- Another version of axiom [15].
  lemma-[15]' : ∀ {j k} {jk : Less j k} -> Rel ⊢ i k ^ 2 • K jk === K jk • X jk
  lemma-[15]' {j} {k} {jk} =
    equational i k ^ 2 • K jk
      by (left-unit reversed)
    equals ε • i k ^ 2 • K jk
      by (left axiom [3] reversed)
    equals K jk ^ 8 • i k ^ 2 • K jk
      by general-assoc auto
    equals K jk ^ 7 • (K jk • i k ^ 2) • K jk
      by (right left axiom [15])
    equals K jk ^ 7 • (X jk • K jk) • K jk
      by (left lemma-K^7)
    equals (K jk • i j • i k) • (X jk • K jk) • K jk
      by general-assoc auto
    equals (K jk • i j) • (i k • X jk) • (K jk • K jk)
      by (right left axiom [10])
    equals (K jk • i j) • (X jk • i j) • (K jk • K jk)
      by general-assoc auto
    equals K jk • (i j • X jk) • i j • (K jk • K jk)
      by (right left lemma-[10]')
    equals K jk • (X jk • i k) • i j • (K jk • K jk)
      by (right right right lemma-K^2)
    equals K jk • (X jk • i k) • i j • (i j ^ 3 • i k ^ 3)
      by general-assoc auto
    equals K jk • (X jk • i k) • (i j • i j ^ 3) • i k ^ 3
      by (right right trans (left axiom [1]) left-unit)
    equals K jk • (X jk • i k) • i k ^ 3
      by general-assoc auto
    equals K jk • X jk • (i k • i k ^ 3)
      by (right trans (right axiom [1]) right-unit)
    equals K jk • X jk

  -- Another version of axiom [15].
  lemma-[15]'' : ∀ {j k} {jk : Less j k} -> Rel ⊢ i j ^ 2 • K jk === K jk • i j ^ 2 • i k ^ 2 • X jk
  lemma-[15]'' {j} {k} {jk} =
    equational i j ^ 2 • K jk
      by symm left-unit
    equals ε • i j ^ 2 • K jk
      by (left symm (axiom [1]))
    equals i k ^ 4 • i j ^ 2 • K jk
      by general-assoc auto
    equals i k ^ 2 • (i k ^ 2 • i j ^ 2) • K jk
      by (right left lemma-comm-powers 2 2 (symm (axiom ([4] {jk = jk}))))
    equals i k ^ 2 • (i j ^ 2 • i k ^ 2) • K jk
      by general-assoc auto
    equals i k ^ 2 • i j ^ 2 • i k ^ 2 • K jk
      by (right right lemma-[15]')
    equals i k ^ 2 • i j ^ 2 • K jk • X jk
      by general-assoc auto
    equals i k • (i k • i j) • i j • K jk • X jk
      by (right left symm (axiom ([4] {jk = jk})))
    equals i k • (i j • i k) • i j • K jk • X jk
      by general-assoc auto
    equals (i k • i j) • (i k • i j) • K jk • X jk
      by (left symm (axiom ([4] {jk = jk})))
    equals (i j • i k) • (i k • i j) • K jk • X jk
      by right (left symm (axiom ([4] {jk = jk})))
    equals (i j • i k) • (i j • i k) • K jk • X jk
      by general-assoc auto
    equals (i j • i k) • (i j • i k • K jk) • X jk
      by (right left symm (axiom [17]))
    equals (i j • i k) • (K jk • i j • i k) • X jk
      by general-assoc auto
    equals (i j • i k • K jk) • i j • i k • X jk
      by (left symm (axiom [17]))
    equals (K jk • i j • i k) • i j • i k • X jk
      by general-assoc auto
    equals (K jk • i j) • (i k • i j) • i k • X jk
      by (right left symm (axiom ([4] {jk = jk})))
    equals (K jk • i j) • (i j • i k) • i k • X jk
      by general-assoc auto
    equals K jk • i j ^ 2 • i k ^ 2 • X jk


  lemma-[16]' : ∀ {j k} {jk : Less j k} -> Rel ⊢ K jk • i k • K jk === i k ^ 3 • K jk • i k ^ 3
  lemma-[16]' {j} {k} {jk} =
    equational K jk • i k • K jk
      by trans (left-unit reversed) (left axiom [1] reversed)
    equals i k ^ 4 • K jk • i k • K jk
      by general-assoc auto
    equals i k ^ 3 • i k • K jk • i k • K jk
      by (right axiom [16] reversed)
    equals i k ^ 3 • K jk • i k ^ 3

  -- Similar to axiom [17]. A scalar matrix commutes with any other
  -- matrix.
  lemma-[17]' : ∀ {j k} {jk : Less j k} -> Rel ⊢ X jk • i j • i k === (i j • i k) • X jk
  lemma-[17]' {j} {k} {jk} =
    equational X jk • i j • i k
      by (right axiom ([4] {jk = jk}))
    equals X jk • i k • i j
      by general-assoc auto
    equals (X jk • i k) • i j
      by (left lemma-[10]' reversed)
    equals (i j • X jk) • i j
      by general-assoc auto
    equals i j • X jk • i j
      by (right axiom [10] reversed)
    equals i j • i k • X jk
      by general-assoc auto
    equals (i j • i k) • X jk


  -- This lemma essentially states that -ZK = -KX, using the 1- and
  -- 2-level generators.
  lemma-ij-ij-ij-ij-Hjk : ∀ {j} {k} {jk : Less j k} -> Rel ⊢ i j ^ 2 • K jk === K jk • i j ^ 2 • i k ^ 2 • X jk
  lemma-ij-ij-ij-ij-Hjk {j} {k} {jk} =
      equational i j ^ 2 • K jk
              by general-assoc auto
          equals i j ^ 2 • ε • K jk
              by right left axiom [1] reversed
          equals i j ^ 2 • i k ^ 4 • K jk
              by general-assoc auto
          equals (i j ^ 2 • i k ^ 2) • i k ^ 2 • K jk
              by left lemma-comm-powers 2 2 comm
          equals (i k ^ 2 • i j ^ 2) • i k ^ 2 • K jk
              by general-assoc auto
          equals i k ^ 2 • (i j ^ 2 • i k ^ 2) • K jk
              by right left lemma-product-power 2 comm reversed
          equals i k ^ 2 • ((i j • i k) ^ 2 • K jk)
              by right lemma-comm-powers 2 1 (trans assoc (axiom [17] reversed))
          equals i k ^ 2 • (K jk • (i j • i k) ^ 2)
              by general-assoc auto
          equals (i k ^ 2 • K jk) • (i j • i k) ^ 2
              by left lemma-[15]'
          equals (K jk • X jk) • (i j • i k) ^ 2
              by general-assoc auto
          equals K jk • (X jk • (i j • i k) ^ 2)
              by right lemma-comm-powers 1 2 ((lemma-[17]'))
          equals K jk • ((i j • i k) ^ 2 • X jk)
              by right left lemma-product-power 2 comm
          equals K jk • ((i j ^ 2 • i k ^ 2) • X jk)
              by general-assoc auto
          equals K jk • i j ^ 2 • i k ^ 2 • X jk
    where
      comm : Rel ⊢ i j • i k === i k • i j
      comm = axiom ([4] {jk = jk})


  -- This lemma essentially states that ZK = HX, using the 1- and
  -- 2-level generators.
  lemma-ik-ik-Hjk : ∀ {j} {k} {jk : Less j k} -> Rel ⊢ i k ^ 2 • K jk === K jk • X jk
  lemma-ik-ik-Hjk = lemma-[15]'


  open Inverse-TwoLevel-Less

  -- This lemma essentially states that XK = KZ, using the 1- and
  -- 2-level generators.
  lemma-Xjk-Hjk : ∀ {j} {k} {jk : Less j k} -> Rel ⊢ X jk • K jk === K jk • i k ^ 2
  lemma-Xjk-Hjk {j} {k} {jk} = axiom [15] reversed
  


  lemma-ij-ik-Hkl : ∀ {j} {k} {l} {kl : Less k l} {jk : Less j k} -> Rel ⊢ i j • i k • K kl === i k • K kl • i j
  lemma-ij-ik-Hkl {j} {k} {l} {kl} {jk} =
    equational i j • i k • K kl
      by symm assoc
    equals (i j • i k) • K kl
      by (left axiom ([4] {jk = jk}))
    equals (i k • i j) • K kl
      by assoc
    equals i k • i j • K kl
      by (right axiom ([6a] {jk = jk}))
    equals i k • K kl • i j



  lemma-13' : ∀ {j k l} {kl : Less k l} {kj : Less k j} {jl : Less j l} -> Rel ⊢ K kl • X kj === X kj • K jl
  lemma-13' {j} {k} {l} {kl} {kj} {jl} =
    equational K kl • X kj
      by trans (symm left-unit) (left symm (axiom [2]))
    equals (X kj • X kj) • K kl • X kj
      by general-assoc auto
    equals X kj • (X kj • K kl) • X kj
      by (right left symm (axiom [13]))
    equals X kj • (K jl • X kj) • X kj
      by cong refl assoc
    equals X kj • K jl • X kj • X kj
      by right cong refl (axiom [2])
    equals X kj • K jl • ε
      by general-assoc auto
    equals X kj • K jl


  lemma-[14'a] : ∀ {j k l} {jl : Less j l} {lk : Less l k} {jk : Less j k} -> Rel ⊢ K jl • X lk === X lk • K jk
  lemma-[14'a] {j} {k} {l} {jl} {lk} {jk} =
    equational K jl • X lk
      by trans (symm left-unit) (left symm (axiom [2]))
    equals (X lk • X lk) • K jl • X lk
      by general-assoc auto
    equals X lk • (X lk • K jl) • X lk
      by (right left symm (axiom [14]))
    equals X lk • (K jk • X lk) • X lk
      by cong refl assoc
    equals X lk • K jk • X lk • X lk
      by (right right axiom [2])
    equals X lk • K jk • ε
      by general-assoc auto
    equals X lk • K jk


  lemma-11' : ∀ {j k l} {kl : Less k l} {kj : Less k j} {jl : Less j l} -> Rel ⊢ X kl • X kj === X kj • X jl
  lemma-11' {j} {k} {l} {kl} {kj} {jl} =
    equational X kl • X kj
      by trans (symm left-unit) (left symm (axiom [2]))
    equals (X kj • X kj) • X kl • X kj
      by general-assoc auto
    equals X kj • (X kj • X kl) • X kj
      by (right left symm (axiom [11]))
    equals X kj • (X jl • X kj) • X kj
      by cong refl assoc
    equals X kj • X jl • X kj • X kj
      by right cong refl (axiom [2])
    equals X kj • X jl • ε
      by general-assoc auto
    equals X kj • X jl


  lemma-12' : ∀ {j k l} {jl : Less j l} {lk : Less l k} {jk : Less j k} -> Rel ⊢ X jl • X lk === X lk • X jk
  lemma-12' {j} {k} {l} {jl} {lk} {jk} =
    equational X jl • X lk
      by trans (symm left-unit) (left symm (axiom [2]))
    equals (X lk • X lk) • X jl • X lk
      by general-assoc auto
    equals X lk • (X lk • X jl) • X lk
      by (right left symm (axiom [12]))
    equals X lk • (X jk • X lk) • X lk
      by cong refl assoc
    equals X lk • X jk • X lk • X lk
      by (right right axiom [2])
    equals X lk • X jk • ε
      by general-assoc auto
    equals X lk • X jk


  -- ----------------------------------------------------------------------
  -- * The rewrite system for 2-level relations.

  -- We define a rewrite system. The basic idea is to reduce the
  -- number of K-generators as much as possible, and otherwise to move
  -- them as far as possible to the left. The details don't matter
  -- that much, as long as the rewrite system "works", i.e., it is
  -- sound (which is proved here) and it proves all the relations we
  -- need (in Soundness.agda).

  step : Step-Function Gen Rel

  step (i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₀₄ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₀₅ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₀₆ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₀₇ ∷ t , at-head lemma-ik-ik-Hjk)

  step (i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₁₄ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₁₅ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₁₆ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₁₇ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₂₄ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₂₅ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₂₆ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₂₇ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₃₄ ∷ X-gen ₃₄ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₃₅ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₃₆ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₃₇ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₄₅ ∷ X-gen ₄₅ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₄₆ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₄₇ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₅₆ ∷ X-gen ₅₆ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₅₇ ∷ t , at-head lemma-ik-ik-Hjk)
  step (i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₆₇ ∷ X-gen ₆₇ ∷ t , at-head lemma-ik-ik-Hjk)


  step (i-gen ₀ ∷ i-gen ₀ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₁ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₁ ∷ i-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-[15]'')
  step (i-gen ₀ ∷ i-gen ₀ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₂ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₂ ∷ i-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-[15]'')
  step (i-gen ₀ ∷ i-gen ₀ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₃ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₃ ∷ i-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-[15]'')
  step (i-gen ₀ ∷ i-gen ₀ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₄ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₄ ∷ i-gen ₄ ∷ X-gen ₀₄ ∷ t , at-head lemma-[15]'')
  step (i-gen ₀ ∷ i-gen ₀ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₅ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₅ ∷ i-gen ₅ ∷ X-gen ₀₅ ∷ t , at-head lemma-[15]'')
  step (i-gen ₀ ∷ i-gen ₀ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₆ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₆ ∷ i-gen ₆ ∷ X-gen ₀₆ ∷ t , at-head lemma-[15]'')
  step (i-gen ₀ ∷ i-gen ₀ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₇ ∷ i-gen ₀ ∷ i-gen ₀ ∷ i-gen ₇ ∷ i-gen ₇ ∷ X-gen ₀₇ ∷ t , at-head lemma-[15]'')

  step (i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₂ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₂ ∷ i-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-[15]'')
  step (i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₃ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₃ ∷ i-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-[15]'')
  step (i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₄ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₄ ∷ i-gen ₄ ∷ X-gen ₁₄ ∷ t , at-head lemma-[15]'')
  step (i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₅ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₅ ∷ i-gen ₅ ∷ X-gen ₁₅ ∷ t , at-head lemma-[15]'')
  step (i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₆ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₆ ∷ i-gen ₆ ∷ X-gen ₁₆ ∷ t , at-head lemma-[15]'')
  step (i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₇ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₇ ∷ i-gen ₇ ∷ X-gen ₁₇ ∷ t , at-head lemma-[15]'')
  step (i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₃ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₃ ∷ i-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-[15]'')
  step (i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₄ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₄ ∷ i-gen ₄ ∷ X-gen ₂₄ ∷ t , at-head lemma-[15]'')
  step (i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₅ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₅ ∷ i-gen ₅ ∷ X-gen ₂₅ ∷ t , at-head lemma-[15]'')
  step (i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₆ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₆ ∷ i-gen ₆ ∷ X-gen ₂₆ ∷ t , at-head lemma-[15]'')
  step (i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₇ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₇ ∷ i-gen ₇ ∷ X-gen ₂₇ ∷ t , at-head lemma-[15]'')
  step (i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₃₄ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₄ ∷ i-gen ₄ ∷ X-gen ₃₄ ∷ t , at-head lemma-[15]'')
  step (i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₃₅ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₅ ∷ i-gen ₅ ∷ X-gen ₃₅ ∷ t , at-head lemma-[15]'')
  step (i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₃₆ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₆ ∷ i-gen ₆ ∷ X-gen ₃₆ ∷ t , at-head lemma-[15]'')
  step (i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₃₇ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₇ ∷ i-gen ₇ ∷ X-gen ₃₇ ∷ t , at-head lemma-[15]'')
  step (i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₄₅ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₅ ∷ i-gen ₅ ∷ X-gen ₄₅ ∷ t , at-head lemma-[15]'')
  step (i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₄₆ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₆ ∷ i-gen ₆ ∷ X-gen ₄₆ ∷ t , at-head lemma-[15]'')
  step (i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₄₇ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₇ ∷ i-gen ₇ ∷ X-gen ₄₇ ∷ t , at-head lemma-[15]'')
  step (i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₅₆ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₆ ∷ i-gen ₆ ∷ X-gen ₅₆ ∷ t , at-head lemma-[15]'')
  step (i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₅₇ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₇ ∷ i-gen ₇ ∷ X-gen ₅₇ ∷ t , at-head lemma-[15]'')
  step (i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₆₇ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₇ ∷ i-gen ₇ ∷ X-gen ₆₇ ∷ t , at-head lemma-[15]'')




  step (K-gen ₀₁ ∷ i-gen ₁ ∷ K-gen ₀₁ ∷ t) = just (i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ K-gen ₀₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₀₂ ∷ i-gen ₂ ∷ K-gen ₀₂ ∷ t) = just (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₀₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₀₃ ∷ i-gen ₃ ∷ K-gen ₀₃ ∷ t) = just (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₀₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₀₄ ∷ i-gen ₄ ∷ K-gen ₀₄ ∷ t) = just (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₀₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₀₅ ∷ i-gen ₅ ∷ K-gen ₀₅ ∷ t) = just (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₀₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₀₆ ∷ i-gen ₆ ∷ K-gen ₀₆ ∷ t) = just (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₀₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₀₇ ∷ i-gen ₇ ∷ K-gen ₀₇ ∷ t) = just (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₀₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-[16]'))

  step (K-gen ₁₂ ∷ i-gen ₂ ∷ K-gen ₁₂ ∷ t) = just (i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ K-gen ₁₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₁₃ ∷ i-gen ₃ ∷ K-gen ₁₃ ∷ t) = just (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₁₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₁₄ ∷ i-gen ₄ ∷ K-gen ₁₄ ∷ t) = just (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₁₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₁₅ ∷ i-gen ₅ ∷ K-gen ₁₅ ∷ t) = just (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₁₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₁₆ ∷ i-gen ₆ ∷ K-gen ₁₆ ∷ t) = just (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₁₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₁₇ ∷ i-gen ₇ ∷ K-gen ₁₇ ∷ t) = just (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₁₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₂₃ ∷ i-gen ₃ ∷ K-gen ₂₃ ∷ t) = just (i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ K-gen ₂₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₂₄ ∷ i-gen ₄ ∷ K-gen ₂₄ ∷ t) = just (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₂₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₂₅ ∷ i-gen ₅ ∷ K-gen ₂₅ ∷ t) = just (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₂₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₂₆ ∷ i-gen ₆ ∷ K-gen ₂₆ ∷ t) = just (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₂₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₂₇ ∷ i-gen ₇ ∷ K-gen ₂₇ ∷ t) = just (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₂₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₃₄ ∷ i-gen ₄ ∷ K-gen ₃₄ ∷ t) = just (i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ K-gen ₃₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₃₅ ∷ i-gen ₅ ∷ K-gen ₃₅ ∷ t) = just (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₃₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₃₆ ∷ i-gen ₆ ∷ K-gen ₃₆ ∷ t) = just (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₃₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₃₇ ∷ i-gen ₇ ∷ K-gen ₃₇ ∷ t) = just (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₃₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₄₅ ∷ i-gen ₅ ∷ K-gen ₄₅ ∷ t) = just (i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ K-gen ₄₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₄₆ ∷ i-gen ₆ ∷ K-gen ₄₆ ∷ t) = just (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₄₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₄₇ ∷ i-gen ₇ ∷ K-gen ₄₇ ∷ t) = just (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₄₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₅₆ ∷ i-gen ₆ ∷ K-gen ₅₆ ∷ t) = just (i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ K-gen ₅₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₅₇ ∷ i-gen ₇ ∷ K-gen ₅₇ ∷ t) = just (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₅₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-[16]'))
  step (K-gen ₆₇ ∷ i-gen ₇ ∷ K-gen ₆₇ ∷ t) = just (i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ K-gen ₆₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head (lemma-[16]'))


  step (i-gen ₀ ∷ i-gen ₁ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₁ ∷ i-gen ₀ ∷ i-gen ₁ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₀ ∷ i-gen ₂ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₂ ∷ i-gen ₀ ∷ i-gen ₂ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₀ ∷ i-gen ₃ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₃ ∷ i-gen ₀ ∷ i-gen ₃ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₀ ∷ i-gen ₄ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₄ ∷ i-gen ₀ ∷ i-gen ₄ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₀ ∷ i-gen ₅ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₅ ∷ i-gen ₀ ∷ i-gen ₅ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₀ ∷ i-gen ₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₆ ∷ i-gen ₀ ∷ i-gen ₆ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₀ ∷ i-gen ₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₇ ∷ i-gen ₀ ∷ i-gen ₇ ∷ t , at-head (axiom [17] reversed))

  step (i-gen ₁ ∷ i-gen ₂ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₂ ∷ i-gen ₁ ∷ i-gen ₂ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₁ ∷ i-gen ₃ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₃ ∷ i-gen ₁ ∷ i-gen ₃ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₁ ∷ i-gen ₄ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₄ ∷ i-gen ₁ ∷ i-gen ₄ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₁ ∷ i-gen ₅ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₅ ∷ i-gen ₁ ∷ i-gen ₅ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₁ ∷ i-gen ₆ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₆ ∷ i-gen ₁ ∷ i-gen ₆ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₁ ∷ i-gen ₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₇ ∷ i-gen ₁ ∷ i-gen ₇ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₂ ∷ i-gen ₃ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₃ ∷ i-gen ₂ ∷ i-gen ₃ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₂ ∷ i-gen ₄ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₄ ∷ i-gen ₂ ∷ i-gen ₄ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₂ ∷ i-gen ₅ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₅ ∷ i-gen ₂ ∷ i-gen ₅ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₂ ∷ i-gen ₆ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₆ ∷ i-gen ₂ ∷ i-gen ₆ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₂ ∷ i-gen ₇ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₇ ∷ i-gen ₂ ∷ i-gen ₇ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₃ ∷ i-gen ₄ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₃₄ ∷ i-gen ₃ ∷ i-gen ₄ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₃ ∷ i-gen ₅ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₃₅ ∷ i-gen ₃ ∷ i-gen ₅ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₃ ∷ i-gen ₆ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₃₆ ∷ i-gen ₃ ∷ i-gen ₆ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₃ ∷ i-gen ₇ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₃₇ ∷ i-gen ₃ ∷ i-gen ₇ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₄ ∷ i-gen ₅ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₄₅ ∷ i-gen ₄ ∷ i-gen ₅ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₄ ∷ i-gen ₆ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₄₆ ∷ i-gen ₄ ∷ i-gen ₆ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₄ ∷ i-gen ₇ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₄₇ ∷ i-gen ₄ ∷ i-gen ₇ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₅ ∷ i-gen ₆ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₅₆ ∷ i-gen ₅ ∷ i-gen ₆ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₅ ∷ i-gen ₇ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₅₇ ∷ i-gen ₅ ∷ i-gen ₇ ∷ t , at-head (axiom [17] reversed))
  step (i-gen ₆ ∷ i-gen ₇ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₆₇ ∷ i-gen ₆ ∷ i-gen ₇ ∷ t , at-head (axiom [17] reversed))

  step (X-gen ₀₁ ∷ i-gen ₀ ∷ t) = just (i-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₀₂ ∷ i-gen ₀ ∷ t) = just (i-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₀₃ ∷ i-gen ₀ ∷ t) = just (i-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₀₄ ∷ i-gen ₀ ∷ t) = just (i-gen ₄ ∷ X-gen ₀₄ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₀₅ ∷ i-gen ₀ ∷ t) = just (i-gen ₅ ∷ X-gen ₀₅ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₀₆ ∷ i-gen ₀ ∷ t) = just (i-gen ₆ ∷ X-gen ₀₆ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₀₇ ∷ i-gen ₀ ∷ t) = just (i-gen ₇ ∷ X-gen ₀₇ ∷ t , at-head (axiom [10] reversed))

  step (X-gen ₁₂ ∷ i-gen ₁ ∷ t) = just (i-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₁₃ ∷ i-gen ₁ ∷ t) = just (i-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₁₄ ∷ i-gen ₁ ∷ t) = just (i-gen ₄ ∷ X-gen ₁₄ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₁₅ ∷ i-gen ₁ ∷ t) = just (i-gen ₅ ∷ X-gen ₁₅ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₁₆ ∷ i-gen ₁ ∷ t) = just (i-gen ₆ ∷ X-gen ₁₆ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₁₇ ∷ i-gen ₁ ∷ t) = just (i-gen ₇ ∷ X-gen ₁₇ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₂₃ ∷ i-gen ₂ ∷ t) = just (i-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₂₄ ∷ i-gen ₂ ∷ t) = just (i-gen ₄ ∷ X-gen ₂₄ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₂₅ ∷ i-gen ₂ ∷ t) = just (i-gen ₅ ∷ X-gen ₂₅ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₂₆ ∷ i-gen ₂ ∷ t) = just (i-gen ₆ ∷ X-gen ₂₆ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₂₇ ∷ i-gen ₂ ∷ t) = just (i-gen ₇ ∷ X-gen ₂₇ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₃₄ ∷ i-gen ₃ ∷ t) = just (i-gen ₄ ∷ X-gen ₃₄ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₃₅ ∷ i-gen ₃ ∷ t) = just (i-gen ₅ ∷ X-gen ₃₅ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₃₆ ∷ i-gen ₃ ∷ t) = just (i-gen ₆ ∷ X-gen ₃₆ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₃₇ ∷ i-gen ₃ ∷ t) = just (i-gen ₇ ∷ X-gen ₃₇ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₄₅ ∷ i-gen ₄ ∷ t) = just (i-gen ₅ ∷ X-gen ₄₅ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₄₆ ∷ i-gen ₄ ∷ t) = just (i-gen ₆ ∷ X-gen ₄₆ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₄₇ ∷ i-gen ₄ ∷ t) = just (i-gen ₇ ∷ X-gen ₄₇ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₅₆ ∷ i-gen ₅ ∷ t) = just (i-gen ₆ ∷ X-gen ₅₆ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₅₇ ∷ i-gen ₅ ∷ t) = just (i-gen ₇ ∷ X-gen ₅₇ ∷ t , at-head (axiom [10] reversed))
  step (X-gen ₆₇ ∷ i-gen ₆ ∷ t) = just (i-gen ₇ ∷ X-gen ₆₇ ∷ t , at-head (axiom [10] reversed))

  step (X-gen ₀₁ ∷ i-gen ₁ ∷ t) = just (i-gen ₀ ∷ X-gen ₀₁ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₀₂ ∷ i-gen ₂ ∷ t) = just (i-gen ₀ ∷ X-gen ₀₂ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₀₃ ∷ i-gen ₃ ∷ t) = just (i-gen ₀ ∷ X-gen ₀₃ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₀₄ ∷ i-gen ₄ ∷ t) = just (i-gen ₀ ∷ X-gen ₀₄ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₀₅ ∷ i-gen ₅ ∷ t) = just (i-gen ₀ ∷ X-gen ₀₅ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₀₆ ∷ i-gen ₆ ∷ t) = just (i-gen ₀ ∷ X-gen ₀₆ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₀₇ ∷ i-gen ₇ ∷ t) = just (i-gen ₀ ∷ X-gen ₀₇ ∷ t , at-head (lemma-[10]' reversed))

  step (X-gen ₁₂ ∷ i-gen ₂ ∷ t) = just (i-gen ₁ ∷ X-gen ₁₂ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₁₃ ∷ i-gen ₃ ∷ t) = just (i-gen ₁ ∷ X-gen ₁₃ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₁₄ ∷ i-gen ₄ ∷ t) = just (i-gen ₁ ∷ X-gen ₁₄ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₁₅ ∷ i-gen ₅ ∷ t) = just (i-gen ₁ ∷ X-gen ₁₅ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₁₆ ∷ i-gen ₆ ∷ t) = just (i-gen ₁ ∷ X-gen ₁₆ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₁₇ ∷ i-gen ₇ ∷ t) = just (i-gen ₁ ∷ X-gen ₁₇ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₂₃ ∷ i-gen ₃ ∷ t) = just (i-gen ₂ ∷ X-gen ₂₃ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₂₄ ∷ i-gen ₄ ∷ t) = just (i-gen ₂ ∷ X-gen ₂₄ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₂₅ ∷ i-gen ₅ ∷ t) = just (i-gen ₂ ∷ X-gen ₂₅ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₂₆ ∷ i-gen ₆ ∷ t) = just (i-gen ₂ ∷ X-gen ₂₆ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₂₇ ∷ i-gen ₇ ∷ t) = just (i-gen ₂ ∷ X-gen ₂₇ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₃₄ ∷ i-gen ₄ ∷ t) = just (i-gen ₃ ∷ X-gen ₃₄ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₃₅ ∷ i-gen ₅ ∷ t) = just (i-gen ₃ ∷ X-gen ₃₅ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₃₆ ∷ i-gen ₆ ∷ t) = just (i-gen ₃ ∷ X-gen ₃₆ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₃₇ ∷ i-gen ₇ ∷ t) = just (i-gen ₃ ∷ X-gen ₃₇ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₄₅ ∷ i-gen ₅ ∷ t) = just (i-gen ₄ ∷ X-gen ₄₅ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₄₆ ∷ i-gen ₆ ∷ t) = just (i-gen ₄ ∷ X-gen ₄₆ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₄₇ ∷ i-gen ₇ ∷ t) = just (i-gen ₄ ∷ X-gen ₄₇ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₅₆ ∷ i-gen ₆ ∷ t) = just (i-gen ₅ ∷ X-gen ₅₆ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₅₇ ∷ i-gen ₇ ∷ t) = just (i-gen ₅ ∷ X-gen ₅₇ ∷ t , at-head (lemma-[10]' reversed))
  step (X-gen ₆₇ ∷ i-gen ₇ ∷ t) = just (i-gen ₆ ∷ X-gen ₆₇ ∷ t , at-head (lemma-[10]' reversed))

  step (X-gen ₀₁ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₁ ∷ i-gen ₁ ∷ i-gen ₁ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₂ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₃ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₄ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₅ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₂ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₂ ∷ i-gen ₂ ∷ i-gen ₂ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₃ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₄ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₅ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₆ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₂₃ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₃ ∷ i-gen ₃ ∷ i-gen ₃ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₂₄ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₂₅ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₂₆ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₂₇ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₃₄ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₃₄ ∷ i-gen ₄ ∷ i-gen ₄ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₃₅ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₃₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₃₆ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₃₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₃₇ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₃₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₄₅ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₄₅ ∷ i-gen ₅ ∷ i-gen ₅ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₄₆ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₄₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₄₇ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₄₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₅₆ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₅₆ ∷ i-gen ₆ ∷ i-gen ₆ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₅₇ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₅₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₆₇ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₆₇ ∷ i-gen ₇ ∷ i-gen ₇ ∷ t , at-head lemma-Xjk-Hjk)


  step (X-gen ₀₁ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₁₂ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₁ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₁ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₁ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₁ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₁ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₂ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₂₃ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₂ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₂ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₂ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₂ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₃ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₃₄ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₃ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₃ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₃ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₄ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₄₅ ∷ X-gen ₀₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₄ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₀₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₄ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₀₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₅ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₅₆ ∷ X-gen ₀₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₅ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₀₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₀₆ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₆₇ ∷ X-gen ₀₆ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₂ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₂₃ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₂ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₂ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₂ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₂ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₃ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₃₄ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₃ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₃ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₃ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₄ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₄₅ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₄ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₄ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₅ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₅₆ ∷ X-gen ₁₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₅ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₁₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₁₆ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₆₇ ∷ X-gen ₁₆ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₃ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₃₄ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₃ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₃ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₃ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₄ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₄₅ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₄ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₄ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₅ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₅₆ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₅ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₂₆ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₆₇ ∷ X-gen ₂₆ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₃₄ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₄₅ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₃₄ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₃₄ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₃₅ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₅₆ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₃₅ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₃₆ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₆₇ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₄₅ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₅₆ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₄₅ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₄₆ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₆₇ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [13])))
  step (X-gen ₅₆ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₆₇ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [13])))


  step (X-gen ₁₂ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₁₃ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₁₄ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₁₅ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₁₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₁₆ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₁₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₁₇ ∷ K-gen ₀₁ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₁₇ ∷ t , at-head (symm (axiom [14])))

  step (X-gen ₂₃ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₄ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₅ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₆ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₂₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₇ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₂₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₃ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₄ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₅ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₆ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₂₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₂₇ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₂₇ ∷ t , at-head (symm (axiom [14])))


  step (X-gen ₃₄ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₅ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₆ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₇ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₃₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₄ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₅ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₆ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₇ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₃₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₄ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₅ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₆ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₃₇ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₃₇ ∷ t , at-head (symm (axiom [14])))



  step (X-gen ₄₅ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₆ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₇ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₅ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₆ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₇ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₅ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₆ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₇ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₅ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₆ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₄₇ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [14])))



  step (X-gen ₅₆ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₇ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₆ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₇ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₆ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₇ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₆ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₇ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₆ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₅₇ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [14])))


  step (X-gen ₆₇ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₆₇ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₆₇ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₆₇ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₆₇ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [14])))
  step (X-gen ₆₇ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [14])))

  step (X-gen ₀₁ ∷ K-gen ₁₂ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₀₁ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₁ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₀₁ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₁ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₀₁ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₁ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₀₁ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₁ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₀₁ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₁ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₀₁ ∷ t , at-head (symm (lemma-13')))


  step (X-gen ₀₂ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₀₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₂ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₀₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₂ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₀₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₂ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₀₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₂ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₀₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₂ ∷ K-gen ₂₃ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₁₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₂ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₁₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₂ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₁₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₂ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₁₂ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₂ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₁₂ ∷ t , at-head (symm (lemma-13')))


  step (X-gen ₀₃ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₀₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₃ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₀₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₃ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₀₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₃ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₀₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₃ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₁₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₃ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₁₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₃ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₁₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₃ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₁₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₃ ∷ K-gen ₃₄ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₂₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₃ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₂₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₃ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₂₃ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₃ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₂₃ ∷ t , at-head (symm (lemma-13')))



  step (X-gen ₀₄ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₀₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₄ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₀₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₄ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₀₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₄ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₁₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₄ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₁₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₄ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₁₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₄ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₂₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₄ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₂₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₄ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₂₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₃₄ ∷ K-gen ₄₅ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₃₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₃₄ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₃₄ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₃₄ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₃₄ ∷ t , at-head (symm (lemma-13')))

  step (X-gen ₀₅ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₀₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₀₅ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₀₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₅ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₁₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₅ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₁₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₅ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₂₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₅ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₂₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₃₅ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₃₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₃₅ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₃₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₄₅ ∷ K-gen ₅₆ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₄₅ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₄₅ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₄₅ ∷ t , at-head (symm (lemma-13')))

  step (X-gen ₀₆ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₀₇ ∷ X-gen ₀₆ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₁₆ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₁₇ ∷ X-gen ₁₆ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₂₆ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₂₇ ∷ X-gen ₂₆ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₃₆ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₃₇ ∷ X-gen ₃₆ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₄₆ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₄₇ ∷ X-gen ₄₆ ∷ t , at-head (symm (lemma-13')))
  step (X-gen ₅₆ ∷ K-gen ₆₇ ∷ t) = just (K-gen ₅₇ ∷ X-gen ₅₆ ∷ t , at-head (symm (lemma-13')))


  step (X-gen ₁₂ ∷ K-gen ₀₂ ∷ t) = just (K-gen ₀₁ ∷ X-gen ₁₂ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₁₃ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₁ ∷ X-gen ₁₃ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₁₄ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₁ ∷ X-gen ₁₄ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₁₅ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₁ ∷ X-gen ₁₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₁₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₁ ∷ X-gen ₁₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₁₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₁ ∷ X-gen ₁₇ ∷ t , at-head (symm (lemma-[14'a])))

  step (X-gen ₂₃ ∷ K-gen ₀₃ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₂₃ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₄ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₂₄ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₅ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₂₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₂₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₂ ∷ X-gen ₂₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₃ ∷ K-gen ₁₃ ∷ t) = just (K-gen ₁₂ ∷ X-gen ₂₃ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₄ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₂ ∷ X-gen ₂₄ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₅ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₂ ∷ X-gen ₂₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₆ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₂ ∷ X-gen ₂₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₂₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₂ ∷ X-gen ₂₇ ∷ t , at-head (symm (lemma-[14'a])))

  step (X-gen ₃₄ ∷ K-gen ₀₄ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₃₄ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₅ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₃₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₃₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₃ ∷ X-gen ₃₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₄ ∷ K-gen ₁₄ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₃₄ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₅ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₃₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₆ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₃₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₃ ∷ X-gen ₃₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₄ ∷ K-gen ₂₄ ∷ t) = just (K-gen ₂₃ ∷ X-gen ₃₄ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₅ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₃ ∷ X-gen ₃₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₆ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₃ ∷ X-gen ₃₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₃₇ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₃ ∷ X-gen ₃₇ ∷ t , at-head (symm (lemma-[14'a])))


  step (X-gen ₄₅ ∷ K-gen ₀₅ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₄₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₄₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₄ ∷ X-gen ₄₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₅ ∷ K-gen ₁₅ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₄₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₆ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₄₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₄ ∷ X-gen ₄₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₅ ∷ K-gen ₂₅ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₄₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₆ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₄₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₇ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₄ ∷ X-gen ₄₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₅ ∷ K-gen ₃₅ ∷ t) = just (K-gen ₃₄ ∷ X-gen ₄₅ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₆ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₃₄ ∷ X-gen ₄₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₄₇ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₃₄ ∷ X-gen ₄₇ ∷ t , at-head (symm (lemma-[14'a])))

  step (X-gen ₅₆ ∷ K-gen ₀₆ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₅₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₅ ∷ X-gen ₅₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₆ ∷ K-gen ₁₆ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₅₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₅ ∷ X-gen ₅₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₆ ∷ K-gen ₂₆ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₅₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₇ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₅ ∷ X-gen ₅₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₆ ∷ K-gen ₃₆ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₅₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₇ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₃₅ ∷ X-gen ₅₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₆ ∷ K-gen ₄₆ ∷ t) = just (K-gen ₄₅ ∷ X-gen ₅₆ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₅₇ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₄₅ ∷ X-gen ₅₇ ∷ t , at-head (symm (lemma-[14'a])))

  step (X-gen ₆₇ ∷ K-gen ₀₇ ∷ t) = just (K-gen ₀₆ ∷ X-gen ₆₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₆₇ ∷ K-gen ₁₇ ∷ t) = just (K-gen ₁₆ ∷ X-gen ₆₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₆₇ ∷ K-gen ₂₇ ∷ t) = just (K-gen ₂₆ ∷ X-gen ₆₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₆₇ ∷ K-gen ₃₇ ∷ t) = just (K-gen ₃₆ ∷ X-gen ₆₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₆₇ ∷ K-gen ₄₇ ∷ t) = just (K-gen ₄₆ ∷ X-gen ₆₇ ∷ t , at-head (symm (lemma-[14'a])))
  step (X-gen ₆₇ ∷ K-gen ₅₇ ∷ t) = just (K-gen ₅₆ ∷ X-gen ₆₇ ∷ t , at-head (symm (lemma-[14'a])))

  -- Catch-all
  step _ = nothing


  X-step : Step-Function Gen Rel
  X-step (X-gen ₀₁ ∷ X-gen ₀₂ ∷ t) = just (X-gen ₁₂ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₁ ∷ X-gen ₀₃ ∷ t) = just (X-gen ₁₃ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₁ ∷ X-gen ₀₄ ∷ t) = just (X-gen ₁₄ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₁ ∷ X-gen ₀₅ ∷ t) = just (X-gen ₁₅ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₁ ∷ X-gen ₀₆ ∷ t) = just (X-gen ₁₆ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₁ ∷ X-gen ₀₇ ∷ t) = just (X-gen ₁₇ ∷ X-gen ₀₁ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₂ ∷ X-gen ₀₃ ∷ t) = just (X-gen ₂₃ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₂ ∷ X-gen ₀₄ ∷ t) = just (X-gen ₂₄ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₂ ∷ X-gen ₀₅ ∷ t) = just (X-gen ₂₅ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₂ ∷ X-gen ₀₆ ∷ t) = just (X-gen ₂₆ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₂ ∷ X-gen ₀₇ ∷ t) = just (X-gen ₂₇ ∷ X-gen ₀₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₃ ∷ X-gen ₀₄ ∷ t) = just (X-gen ₃₄ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₃ ∷ X-gen ₀₅ ∷ t) = just (X-gen ₃₅ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₃ ∷ X-gen ₀₆ ∷ t) = just (X-gen ₃₆ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₃ ∷ X-gen ₀₇ ∷ t) = just (X-gen ₃₇ ∷ X-gen ₀₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₄ ∷ X-gen ₀₅ ∷ t) = just (X-gen ₄₅ ∷ X-gen ₀₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₄ ∷ X-gen ₀₆ ∷ t) = just (X-gen ₄₆ ∷ X-gen ₀₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₄ ∷ X-gen ₀₇ ∷ t) = just (X-gen ₄₇ ∷ X-gen ₀₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₅ ∷ X-gen ₀₆ ∷ t) = just (X-gen ₅₆ ∷ X-gen ₀₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₅ ∷ X-gen ₀₇ ∷ t) = just (X-gen ₅₇ ∷ X-gen ₀₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₀₆ ∷ X-gen ₀₇ ∷ t) = just (X-gen ₆₇ ∷ X-gen ₀₆ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₂ ∷ X-gen ₁₃ ∷ t) = just (X-gen ₂₃ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₂ ∷ X-gen ₁₄ ∷ t) = just (X-gen ₂₄ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₂ ∷ X-gen ₁₅ ∷ t) = just (X-gen ₂₅ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₂ ∷ X-gen ₁₆ ∷ t) = just (X-gen ₂₆ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₂ ∷ X-gen ₁₇ ∷ t) = just (X-gen ₂₇ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₃ ∷ X-gen ₁₄ ∷ t) = just (X-gen ₃₄ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₃ ∷ X-gen ₁₅ ∷ t) = just (X-gen ₃₅ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₃ ∷ X-gen ₁₆ ∷ t) = just (X-gen ₃₆ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₃ ∷ X-gen ₁₇ ∷ t) = just (X-gen ₃₇ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₄ ∷ X-gen ₁₅ ∷ t) = just (X-gen ₄₅ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₄ ∷ X-gen ₁₆ ∷ t) = just (X-gen ₄₆ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₄ ∷ X-gen ₁₇ ∷ t) = just (X-gen ₄₇ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₅ ∷ X-gen ₁₆ ∷ t) = just (X-gen ₅₆ ∷ X-gen ₁₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₅ ∷ X-gen ₁₇ ∷ t) = just (X-gen ₅₇ ∷ X-gen ₁₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₁₆ ∷ X-gen ₁₇ ∷ t) = just (X-gen ₆₇ ∷ X-gen ₁₆ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₃ ∷ X-gen ₂₄ ∷ t) = just (X-gen ₃₄ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₃ ∷ X-gen ₂₅ ∷ t) = just (X-gen ₃₅ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₃ ∷ X-gen ₂₆ ∷ t) = just (X-gen ₃₆ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₃ ∷ X-gen ₂₇ ∷ t) = just (X-gen ₃₇ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₄ ∷ X-gen ₂₅ ∷ t) = just (X-gen ₄₅ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₄ ∷ X-gen ₂₆ ∷ t) = just (X-gen ₄₆ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₄ ∷ X-gen ₂₇ ∷ t) = just (X-gen ₄₇ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₅ ∷ X-gen ₂₆ ∷ t) = just (X-gen ₅₆ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₅ ∷ X-gen ₂₇ ∷ t) = just (X-gen ₅₇ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₂₆ ∷ X-gen ₂₇ ∷ t) = just (X-gen ₆₇ ∷ X-gen ₂₆ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₃₄ ∷ X-gen ₃₅ ∷ t) = just (X-gen ₄₅ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₃₄ ∷ X-gen ₃₆ ∷ t) = just (X-gen ₄₆ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₃₄ ∷ X-gen ₃₇ ∷ t) = just (X-gen ₄₇ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₃₅ ∷ X-gen ₃₆ ∷ t) = just (X-gen ₅₆ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₃₅ ∷ X-gen ₃₇ ∷ t) = just (X-gen ₅₇ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₃₆ ∷ X-gen ₃₇ ∷ t) = just (X-gen ₆₇ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₄₅ ∷ X-gen ₄₆ ∷ t) = just (X-gen ₅₆ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₄₅ ∷ X-gen ₄₇ ∷ t) = just (X-gen ₅₇ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₄₆ ∷ X-gen ₄₇ ∷ t) = just (X-gen ₆₇ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [11])))
  X-step (X-gen ₅₆ ∷ X-gen ₅₇ ∷ t) = just (X-gen ₆₇ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [11])))


  X-step (X-gen ₁₂ ∷ X-gen ₀₁ ∷ t) = just (X-gen ₀₂ ∷ X-gen ₁₂ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₁₃ ∷ X-gen ₀₁ ∷ t) = just (X-gen ₀₃ ∷ X-gen ₁₃ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₁₄ ∷ X-gen ₀₁ ∷ t) = just (X-gen ₀₄ ∷ X-gen ₁₄ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₁₅ ∷ X-gen ₀₁ ∷ t) = just (X-gen ₀₅ ∷ X-gen ₁₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₁₆ ∷ X-gen ₀₁ ∷ t) = just (X-gen ₀₆ ∷ X-gen ₁₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₁₇ ∷ X-gen ₀₁ ∷ t) = just (X-gen ₀₇ ∷ X-gen ₁₇ ∷ t , at-head (symm (axiom [12])))

  X-step (X-gen ₂₃ ∷ X-gen ₀₂ ∷ t) = just (X-gen ₀₃ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₄ ∷ X-gen ₀₂ ∷ t) = just (X-gen ₀₄ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₅ ∷ X-gen ₀₂ ∷ t) = just (X-gen ₀₅ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₆ ∷ X-gen ₀₂ ∷ t) = just (X-gen ₀₆ ∷ X-gen ₂₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₇ ∷ X-gen ₀₂ ∷ t) = just (X-gen ₀₇ ∷ X-gen ₂₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₃ ∷ X-gen ₁₂ ∷ t) = just (X-gen ₁₃ ∷ X-gen ₂₃ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₄ ∷ X-gen ₁₂ ∷ t) = just (X-gen ₁₄ ∷ X-gen ₂₄ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₅ ∷ X-gen ₁₂ ∷ t) = just (X-gen ₁₅ ∷ X-gen ₂₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₆ ∷ X-gen ₁₂ ∷ t) = just (X-gen ₁₆ ∷ X-gen ₂₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₂₇ ∷ X-gen ₁₂ ∷ t) = just (X-gen ₁₇ ∷ X-gen ₂₇ ∷ t , at-head (symm (axiom [12])))


  X-step (X-gen ₃₄ ∷ X-gen ₀₃ ∷ t) = just (X-gen ₀₄ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₅ ∷ X-gen ₀₃ ∷ t) = just (X-gen ₀₅ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₆ ∷ X-gen ₀₃ ∷ t) = just (X-gen ₀₆ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₇ ∷ X-gen ₀₃ ∷ t) = just (X-gen ₀₇ ∷ X-gen ₃₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₄ ∷ X-gen ₁₃ ∷ t) = just (X-gen ₁₄ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₅ ∷ X-gen ₁₃ ∷ t) = just (X-gen ₁₅ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₆ ∷ X-gen ₁₃ ∷ t) = just (X-gen ₁₆ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₇ ∷ X-gen ₁₃ ∷ t) = just (X-gen ₁₇ ∷ X-gen ₃₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₄ ∷ X-gen ₂₃ ∷ t) = just (X-gen ₂₄ ∷ X-gen ₃₄ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₅ ∷ X-gen ₂₃ ∷ t) = just (X-gen ₂₅ ∷ X-gen ₃₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₆ ∷ X-gen ₂₃ ∷ t) = just (X-gen ₂₆ ∷ X-gen ₃₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₃₇ ∷ X-gen ₂₃ ∷ t) = just (X-gen ₂₇ ∷ X-gen ₃₇ ∷ t , at-head (symm (axiom [12])))



  X-step (X-gen ₄₅ ∷ X-gen ₀₄ ∷ t) = just (X-gen ₀₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₆ ∷ X-gen ₀₄ ∷ t) = just (X-gen ₀₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₇ ∷ X-gen ₀₄ ∷ t) = just (X-gen ₀₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₅ ∷ X-gen ₁₄ ∷ t) = just (X-gen ₁₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₆ ∷ X-gen ₁₄ ∷ t) = just (X-gen ₁₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₇ ∷ X-gen ₁₄ ∷ t) = just (X-gen ₁₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₅ ∷ X-gen ₂₄ ∷ t) = just (X-gen ₂₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₆ ∷ X-gen ₂₄ ∷ t) = just (X-gen ₂₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₇ ∷ X-gen ₂₄ ∷ t) = just (X-gen ₂₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₅ ∷ X-gen ₃₄ ∷ t) = just (X-gen ₃₅ ∷ X-gen ₄₅ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₆ ∷ X-gen ₃₄ ∷ t) = just (X-gen ₃₆ ∷ X-gen ₄₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₄₇ ∷ X-gen ₃₄ ∷ t) = just (X-gen ₃₇ ∷ X-gen ₄₇ ∷ t , at-head (symm (axiom [12])))



  X-step (X-gen ₅₆ ∷ X-gen ₀₅ ∷ t) = just (X-gen ₀₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₇ ∷ X-gen ₀₅ ∷ t) = just (X-gen ₀₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₆ ∷ X-gen ₁₅ ∷ t) = just (X-gen ₁₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₇ ∷ X-gen ₁₅ ∷ t) = just (X-gen ₁₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₆ ∷ X-gen ₂₅ ∷ t) = just (X-gen ₂₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₇ ∷ X-gen ₂₅ ∷ t) = just (X-gen ₂₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₆ ∷ X-gen ₃₅ ∷ t) = just (X-gen ₃₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₇ ∷ X-gen ₃₅ ∷ t) = just (X-gen ₃₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₆ ∷ X-gen ₄₅ ∷ t) = just (X-gen ₄₆ ∷ X-gen ₅₆ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₅₇ ∷ X-gen ₄₅ ∷ t) = just (X-gen ₄₇ ∷ X-gen ₅₇ ∷ t , at-head (symm (axiom [12])))


  X-step (X-gen ₆₇ ∷ X-gen ₀₆ ∷ t) = just (X-gen ₀₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₆₇ ∷ X-gen ₁₆ ∷ t) = just (X-gen ₁₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₆₇ ∷ X-gen ₂₆ ∷ t) = just (X-gen ₂₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₆₇ ∷ X-gen ₃₆ ∷ t) = just (X-gen ₃₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₆₇ ∷ X-gen ₄₆ ∷ t) = just (X-gen ₄₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [12])))
  X-step (X-gen ₆₇ ∷ X-gen ₅₆ ∷ t) = just (X-gen ₅₇ ∷ X-gen ₆₇ ∷ t , at-head (symm (axiom [12])))

  X-step _ = nothing

-- Finally, we instantiate the Step-With-Standardization module with
-- the two rewrite relations defined above, to obtain a tactic
-- 'rewrite-twolevel'.

module TwoLevel-Less-Rewrite = Step-With-Standardization (step-cong (TwoLevel-Less-Step-Order.step then TwoLevel-Less-Step.step)) Commuting-TwoLevel-Less.comm-canonical Commuting-TwoLevel-Less.lemma-comm-canonical renaming (general-rewrite to rewrite-twolevel)


module TwoLevel-Less-Rewrite2 = Step-With-Standardization (step-cong (TwoLevel-Less-Step-Order.step then TwoLevel-Less-Step.X-step)) Commuting-TwoLevel-Less.comm-canonical Commuting-TwoLevel-Less.lemma-comm-canonical renaming (general-rewrite to rewrite-twolevel)


module TwoLevel-Less-Rewrite3 = Step-With-Standardization (step-cong (TwoLevel-Less-Step-Order.step then TwoLevel-Less-Step.step then TwoLevel-Less-Step.X-step)) Commuting-TwoLevel-Less.comm-canonical Commuting-TwoLevel-Less.lemma-comm-canonical renaming (general-rewrite to rewrite-twolevel)


