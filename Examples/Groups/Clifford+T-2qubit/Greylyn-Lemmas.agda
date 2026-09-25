------------------------------------------------------------------------
-- Presentations of groups
--
-- Greylyn-Lemmas: automation for Greylyn's 1- and 2-level operators:
-- commutation and ordering of generators, inverses, and two rewrite
-- systems (ordering, and two-level normalisation) up to commutativity.
-- Ported from the Agda code accompanying Bian and Selinger, "Generators
-- and relations for 2-qubit Clifford+T operators" (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Greylyn-Lemmas where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≤?_ ; _≟_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no ; does)
open import Presentation.Tactics.Equality as Eq using (_≡_)

open import Notations using (auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open import Presentation.Tactics.Lists
open import Presentation.Tactics.Words
open import Examples.Groups.Clifford+T-2qubit.Generator as Generator

open Rewriting

-- ----------------------------------------------------------------------
-- * Data required for applying monoid tactics to Greylyn generators

module Greylyn-Data where

  -- Here, we provide some basic data about which 1- and 2-level
  -- generators commute, an ordering on the generators, and
  -- information about their inverses. This is then used to
  -- instantiate various tactics.

  open Monoid-Equational
  open Associative
  open Greylyn

  -- Convert an index to a natural number.
  nat-of-index : Index -> ℕ
  nat-of-index ₀ = 0
  nat-of-index ₁ = 1
  nat-of-index ₂ = 2
  nat-of-index ₃ = 3

  infix 8 _!=?_

  -- A decidable not-equal relation on indices.
  _!=?_ : (j k : Index) -> Maybe (Neq j k)
  ₀ !=? ₁ = just ₀₁
  ₀ !=? ₂ = just ₀₂
  ₀ !=? ₃ = just ₀₃
  ₁ !=? ₂ = just ₁₂
  ₁ !=? ₃ = just ₁₃
  ₂ !=? ₃ = just ₂₃
  ₁ !=? ₀ = just ₁₀
  ₂ !=? ₀ = just ₂₀
  ₃ !=? ₀ = just ₃₀
  ₂ !=? ₁ = just ₂₁
  ₃ !=? ₁ = just ₃₁
  ₃ !=? ₂ = just ₃₂
  _ !=? _ = nothing

  -- Information on the commutativity of generators.
  comm : (x y : Generator) -> Maybe (commutes Greylyn.Rel x y)
  comm (ω-gen j) (ω-gen k) with j !=? k
  ... | nothing = nothing
  ... | just jk = just (axiom ([4] {jk = jk}))
  comm (ω-gen l) (H-gen {j} {k} jk) with l !=? j | l !=? k
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just lj | just lk = just (axiom ([5] {lj = lj} {lk = lk}))
  comm (ω-gen l) (X-gen {j} {k} jk) with l !=? j | l !=? k
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just lj | just lk = just (axiom ([6] {lj = lj} {lk = lk}))
  comm (H-gen {j} {k} jk) (ω-gen l) with l !=? j | l !=? k
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just lj | just lk = just (axiom ([5] {lj = lj} {lk = lk}) reversed)
  comm (H-gen {j} {k} jk) (H-gen {l} {t} lt) with l !=? j | l !=? k | t !=? j | t !=? k
  ... | nothing | _ | _ | _ = nothing
  ... | _ | nothing | _ | _ = nothing
  ... | _ | _ | nothing | _ = nothing
  ... | _ | _ | _ | nothing = nothing
  ... | just lj | just lk | just tj | just tk = just (axiom ([7] {lj = lj} {lk = lk} {tj = tj} {tk = tk}))
  comm (H-gen {j} {k} jk) (X-gen {l} {t} lt) with l !=? j | l !=? k | t !=? j | t !=? k
  ... | nothing | _ | _ | _ = nothing
  ... | _ | nothing | _ | _ = nothing
  ... | _ | _ | nothing | _ = nothing
  ... | _ | _ | _ | nothing = nothing
  ... | just lj | just lk | just tj | just tk = just (axiom ([8] {lj = lj} {lk = lk} {tj = tj} {tk = tk}))
  comm (X-gen {j} {k} jk) (ω-gen l) with l !=? j | l !=? k
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just lj | just lk = just (axiom ([6] {lj = lj} {lk = lk}) reversed)
  comm (X-gen {l} {t} lt) (H-gen {j} {k} jk) with l !=? j | l !=? k | t !=? j | t !=? k
  ... | nothing | _ | _ | _ = nothing
  ... | _ | nothing | _ | _ = nothing
  ... | _ | _ | nothing | _ = nothing
  ... | _ | _ | _ | nothing = nothing
  ... | just lj | just lk | just tj | just tk = just (axiom ([8] {lj = lj} {lk = lk} {tj = tj} {tk = tk}) reversed)
  comm (X-gen {j} {k} jk) (X-gen {l} {t} lt) with l !=? j | l !=? k | t !=? j | t !=? k
  ... | nothing | _ | _ | _ = nothing
  ... | _ | nothing | _ | _ = nothing
  ... | _ | _ | nothing | _ = nothing
  ... | _ | _ | _ | nothing = nothing
  ... | just lj | just lk | just tj | just tk = just (axiom ([9] {lj = lj} {lk = lk} {tj = tj} {tk = tk}))

  -- We rank the generators to induce an order on them.
  rank : Greylyn.Generator -> ℕ
  rank (ω-gen j) = 1 + 9 * (nat-of-index j)
  rank (X-gen {j} {k} jk) = 2 + 3 * (nat-of-index k) + 9 * (nat-of-index j)
  rank (H-gen {j} {k} jk) = 0 + 3 * (nat-of-index k) + 9 * (nat-of-index j)

  -- An ordering of the generators.
  less : Greylyn.Generator -> Greylyn.Generator -> Bool
  less g h = does (rank g ≤? rank h)

  -- Information about the inverses of the generators.
  group-like : Grouplike Greylyn.Rel
  group-like (ω-gen j) = (ω j ^ 7 , up-to-assoc auto (axiom ([1] {j})))
  group-like (X-gen jk) = (X jk , axiom [3])
  group-like (H-gen jk) = (H jk , axiom [2])

-- Now we instantiate various modules with this information, to obtain
-- lemmas and tactics:

module Commuting-Greylyn = Commuting Greylyn.Generator Greylyn.Rel Greylyn-Data.comm Greylyn-Data.less
module Inverse-Greylyn = Inverse Greylyn.Generator Greylyn.Rel Greylyn-Data.group-like

-- ----------------------------------------------------------------------
-- * Rewrite rules for order of generators

module Greylyn-Step-Order where

  -- Here, we provide a rewrite rule for reducing powers of
  -- generators. This is helpful in defining the more general rewrite
  -- system below.

  open InContext
  open Greylyn

  -- Step function: Rewrite powers of generators modulo their order.
  step : Step-Function Generator Greylyn.Rel
  step (ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ t) = just (t , at-head (axiom [1]))
  step (ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ t) = just (t , at-head (axiom [1]))
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ t) = just (t , at-head (axiom [1]))
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ t) = just (t , at-head (axiom [1]))
  
  step (H-gen ₀₁ ∷ H-gen ₀₁ ∷ t) = just (t , at-head (axiom [2]))
  step (H-gen ₀₂ ∷ H-gen ₀₂ ∷ t) = just (t , at-head (axiom [2]))
  step (H-gen ₀₃ ∷ H-gen ₀₃ ∷ t) = just (t , at-head (axiom [2]))
  step (H-gen ₁₂ ∷ H-gen ₁₂ ∷ t) = just (t , at-head (axiom [2]))
  step (H-gen ₁₃ ∷ H-gen ₁₃ ∷ t) = just (t , at-head (axiom [2]))
  step (H-gen ₂₃ ∷ H-gen ₂₃ ∷ t) = just (t , at-head (axiom [2]))

  step (X-gen ₀₁ ∷ X-gen ₀₁ ∷ t) = just (t , at-head (axiom [3]))
  step (X-gen ₀₂ ∷ X-gen ₀₂ ∷ t) = just (t , at-head (axiom [3]))
  step (X-gen ₀₃ ∷ X-gen ₀₃ ∷ t) = just (t , at-head (axiom [3]))
  step (X-gen ₁₂ ∷ X-gen ₁₂ ∷ t) = just (t , at-head (axiom [3]))
  step (X-gen ₁₃ ∷ X-gen ₁₃ ∷ t) = just (t , at-head (axiom [3]))
  step (X-gen ₂₃ ∷ X-gen ₂₃ ∷ t) = just (t , at-head (axiom [3]))

  step _ = nothing

module Greylyn-Rewrite-Order = Step-With-Standardization (step-cong Greylyn-Step-Order.step) Commuting-Greylyn.comm-canonical Commuting-Greylyn.lemma-comm-canonical renaming (general-rewrite to rewrite-order)

-- ----------------------------------------------------------------------
-- * A set of rewrite rules for 2-level Greylyn operators

module Greylyn-Step-Twolevel where

  open Monoid-Equational
  open Monoid-Lemmas
  open Associative
  open InContext
  open Greylyn

  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- We prove various lemmas that are needed to justify the
  -- correctness of the rewrite relation below. Most of these lemmas
  -- have little intuitive value; they are basically just what is
  -- needed to make the rewriting work.

  -- A trivial lemma about indices: j < k implies j != k.
  lemma-less : ∀ {j k} -> Less j k -> Neq j k
  lemma-less ₀₁ = ₀₁
  lemma-less ₀₂ = ₀₂
  lemma-less ₀₃ = ₀₃
  lemma-less ₁₂ = ₁₂
  lemma-less ₁₃ = ₁₃
  lemma-less ₂₃ = ₂₃

  -- This lemma essentially states that -ZH = -HX, using the 1- and
  -- 2-level generators.
  lemma-ωj-ωj-ωj-ωj-Hjk : ∀ {j} {k} {jk : Less j k} -> Greylyn.Rel ⊢ ω j ^ 4 • H jk === H jk • ω j ^ 4 • ω k ^ 4 • X jk
  lemma-ωj-ωj-ωj-ωj-Hjk {j} {k} {jk} =
      equational ω j ^ 4 • H jk
              by general-assoc auto
          equals ω j ^ 4 • ε • H jk
              by right left axiom [1] reversed
          equals ω j ^ 4 • ω k ^ 8 • H jk
              by general-assoc auto
          equals (ω j ^ 4 • ω k ^ 4) • ω k ^ 4 • H jk
              by left lemma-comm-powers 4 4 comm
          equals (ω k ^ 4 • ω j ^ 4) • ω k ^ 4 • H jk
              by general-assoc auto
          equals ω k ^ 4 • ((ω j ^ 4 • ω k ^ 4) • H jk)
              by right left lemma-product-power 4 comm reversed
          equals ω k ^ 4 • ((ω j • ω k) ^ 4 • H jk)
              by right lemma-comm-powers 4 1 (trans assoc (axiom [17]))
          equals ω k ^ 4 • (H jk • (ω j • ω k) ^ 4)
              by general-assoc auto
          equals (ω k ^ 4 • H jk) • (ω j • ω k) ^ 4
              by left axiom [18] reversed
          equals (H jk • X jk) • (ω j • ω k) ^ 4
              by general-assoc auto
          equals H jk • (X jk • (ω j • ω k) ^ 4)
              by right lemma-comm-powers 4 1 (trans assoc (axiom [16])) reversed
          equals H jk • ((ω j • ω k) ^ 4 • X jk)
              by right left lemma-product-power 4 comm
          equals H jk • ((ω j ^ 4 • ω k ^ 4) • X jk)
              by general-assoc auto
          equals H jk • ω j ^ 4 • ω k ^ 4 • X jk
    where
      comm : Greylyn.Rel ⊢ ω j • ω k === ω k • ω j
      comm = axiom ([4] {jk = lemma-less jk})

  -- A lemma about ω and H.
  lemma-ωk-Hjk : ∀ {j} {k} {jk : Less j k} -> Greylyn.Rel ⊢ ω k • H jk === ω j ^ 3 • H jk • ω j ^ 5 • ω k ^ 5 • X jk
  lemma-ωk-Hjk {j} {k} {jk} =
      equational ω k • H jk  
              by general-assoc auto
          equals ε • ω k • H jk
              by left axiom [1] reversed
          equals ω j ^ 8 • ω k • H jk
              by general-assoc auto
          equals ω j ^ 7 • (ω j • ω k • H jk)
              by right (axiom [17])
          equals ω j ^ 7 • (H jk • ω j • ω k)
              by general-assoc auto
          equals ω j ^ 3 • (ω j ^ 4 • H jk) • (ω j • ω k)
              by right left lemma-ωj-ωj-ωj-ωj-Hjk
          equals ω j ^ 3 • (H jk • ω j ^ 4 • ω k ^ 4 • X jk) • (ω j • ω k)
              by general-assoc auto
          equals (ω j ^ 3 • H jk • ω j ^ 4 • ω k ^ 4) • (X jk • ω j • ω k)
              by right axiom [16] reversed
          equals (ω j ^ 3 • H jk • ω j ^ 4 • ω k ^ 4) • (ω j • ω k • X jk)
              by general-assoc auto
          equals (ω j ^ 3 • H jk • ω j ^ 4) • (ω k ^ 4 • ω j) • (ω k • X jk)
              by right left lemma-comm-powers 1 4 comm reversed
          equals (ω j ^ 3 • H jk • ω j ^ 4) • (ω j • ω k ^ 4) • (ω k • X jk)
              by general-assoc auto
          equals ω j ^ 3 • H jk • ω j ^ 5 • ω k ^ 5 • X jk
    where
      comm : Greylyn.Rel ⊢ ω j • ω k === ω k • ω j
      comm = axiom ([4] {jk = lemma-less jk})

  -- Another lemma about ω and H.
  lemma-ωk-ωk-Hjk : ∀ {j} {k} {jk : Less j k} -> Greylyn.Rel ⊢ ω k ^ 2 • H jk === ω j ^ 2 • H jk • ω j ^ 6 • ω k ^ 6 • X jk
  lemma-ωk-ωk-Hjk {j} {k} {jk} =
      equational ω k ^ 2 • H jk
              by general-assoc auto
          equals ε • ω k ^ 2 • H jk
              by left axiom [1] reversed
          equals ω j ^ 8 • ω k ^ 2 • H jk
              by general-assoc auto
          equals ω j ^ 6 • ((ω j ^ 2 • ω k ^ 2) • H jk)
              by right left lemma-product-power 2 comm reversed
          equals ω j ^ 6 • ((ω j • ω k) ^ 2 • H jk)
              by right lemma-comm-powers 2 1 (trans assoc (axiom [17]))
          equals ω j ^ 6 • (H jk • (ω j • ω k) ^ 2)
              by general-assoc auto
          equals ω j ^ 2 • (ω j ^ 4 • H jk) • (ω j • ω k) ^ 2
              by right left lemma-ωj-ωj-ωj-ωj-Hjk
          equals ω j ^ 2 • (H jk • ω j ^ 4 • ω k ^ 4 • X jk) • (ω j • ω k) ^ 2
              by general-assoc auto
          equals (ω j ^ 2 • H jk • ω j ^ 4 • ω k ^ 4) • (X jk • (ω j • ω k) ^ 2)
              by right lemma-comm-powers 2 1 (trans assoc (axiom [16])) reversed
          equals (ω j ^ 2 • H jk • ω j ^ 4 • ω k ^ 4) • ((ω j • ω k) ^ 2 • X jk)
              by right left lemma-product-power 2 comm
          equals (ω j ^ 2 • H jk • ω j ^ 4 • ω k ^ 4) • ((ω j ^ 2 • ω k ^ 2) • X jk)
              by general-assoc auto
          equals (ω j ^ 2 • H jk • ω j ^ 4) • (ω k ^ 4 • ω j ^ 2) • (ω k ^ 2 • X jk)
              by right left lemma-comm-powers 2 4 comm reversed
          equals (ω j ^ 2 • H jk • ω j ^ 4) • (ω j ^ 2 • ω k ^ 4) • (ω k ^ 2 • X jk)
              by general-assoc auto
          equals ω j ^ 2 • H jk • ω j ^ 6 • ω k ^ 6 • X jk
    where
      comm : Greylyn.Rel ⊢ ω j • ω k === ω k • ω j
      comm = axiom ([4] {jk = lemma-less jk})

  -- Another lemma about ω and H.
  lemma-ωk-ωk-ωk-Hjk : ∀ {j} {k} {jk : Less j k} -> Greylyn.Rel ⊢ ω k ^ 3 • H jk === ω j • H jk • ω j ^ 7 • ω k ^ 7 • X jk
  lemma-ωk-ωk-ωk-Hjk {j} {k} {jk} =
      equational ω k ^ 3 • H jk
              by general-assoc auto
          equals ε • ω k ^ 3 • H jk
              by left axiom [1] reversed
          equals ω j ^ 8 • ω k ^ 3 • H jk
              by general-assoc auto
          equals ω j ^ 5 • ((ω j ^ 3 • ω k ^ 3) • H jk)
              by right left lemma-product-power 3 comm reversed
          equals ω j ^ 5 • ((ω j • ω k) ^ 3 • H jk)
              by right lemma-comm-powers 3 1 (trans assoc (axiom [17]))
          equals ω j ^ 5 • (H jk • (ω j • ω k) ^ 3)
              by general-assoc auto
          equals ω j • (ω j ^ 4 • H jk) • (ω j • ω k) ^ 3
              by right left lemma-ωj-ωj-ωj-ωj-Hjk
          equals ω j • (H jk • ω j ^ 4 • ω k ^ 4 • X jk) • (ω j • ω k) ^ 3
              by general-assoc auto
          equals (ω j • H jk • ω j ^ 4 • ω k ^ 4) • (X jk • (ω j • ω k) ^ 3)
              by right lemma-comm-powers 3 1 (trans assoc (axiom [16])) reversed
          equals (ω j • H jk • ω j ^ 4 • ω k ^ 4) • ((ω j • ω k) ^ 3 • X jk)
              by right left lemma-product-power 3 comm
          equals (ω j • H jk • ω j ^ 4 • ω k ^ 4) • ((ω j ^ 3 • ω k ^ 3) • X jk)
              by general-assoc auto
          equals (ω j • H jk • ω j ^ 4) • (ω k ^ 4 • ω j ^ 3) • (ω k ^ 3 • X jk)
              by right left lemma-comm-powers 3 4 comm reversed
          equals (ω j • H jk • ω j ^ 4) • (ω j ^ 3 • ω k ^ 4) • (ω k ^ 3 • X jk)
              by general-assoc auto
          equals ω j • H jk • ω j ^ 7 • ω k ^ 7 • X jk
    where
      comm : Greylyn.Rel ⊢ ω j • ω k === ω k • ω j
      comm = axiom ([4] {jk = lemma-less jk})

  -- This lemma essentially states that ZH = HX, using the 1- and
  -- 2-level generators.
  lemma-ωk-ωk-ωk-ωk-Hjk : ∀ {j} {k} {jk : Less j k} -> Greylyn.Rel ⊢ ω k ^ 4 • H jk === H jk • X jk
  lemma-ωk-ωk-ωk-ωk-Hjk {j} {k} {jk} =
      equational ω k ^ 4 • H jk
              by axiom [18] reversed
          equals H jk • X jk

  -- Another lemma about ω and H.
  lemma-Hjk-ωj-ωj-Hjk : ∀ {j} {k} {jk : Less j k} -> Greylyn.Rel ⊢ H jk • ω j • ω j • H jk === ω j ^ 2 • H jk • ω j • ω k ^ 7 • X jk
  lemma-Hjk-ωj-ωj-Hjk {j} {k} {jk} =
      equational H jk • ω j • ω j • H jk
              by general-assoc auto
          equals H jk • ω j ^ 2 • H jk
              by axiom [19]
          equals ω j ^ 6 • H jk • ω j ^ 3 • ω k ^ 5
              by general-assoc auto
          equals ω j ^ 2 • (ω j ^ 4 • H jk) • (ω j ^ 3 • ω k ^ 5)
              by right left lemma-ωj-ωj-ωj-ωj-Hjk
          equals ω j ^ 2 • (H jk • ω j ^ 4 • ω k ^ 4 • X jk) • (ω j ^ 3 • ω k ^ 5)
              by general-assoc auto
          equals (ω j ^ 2 • H jk • ω j ^ 4 • ω k ^ 4) • (X jk • ω j ^ 3) • ω k ^ 5
              by right left lemma-comm-power 3 (axiom [11])
          equals (ω j ^ 2 • H jk • ω j ^ 4 • ω k ^ 4) • (ω k ^ 3 • X jk) • ω k ^ 5
              by general-assoc auto
          equals (ω j ^ 2 • H jk • ω j ^ 4 • ω k ^ 7) • (X jk • ω k ^ 5)
              by right lemma-comm-power 5 (axiom [10])
          equals (ω j ^ 2 • H jk • ω j ^ 4 • ω k ^ 7) • (ω j ^ 5 • X jk)
              by general-assoc auto
          equals (ω j ^ 2 • H jk • ω j ^ 4) • (ω k ^ 7 • ω j ^ 5) • X jk
              by right left lemma-comm-powers 5 7 comm reversed
          equals (ω j ^ 2 • H jk • ω j ^ 4) • (ω j ^ 5 • ω k ^ 7) • X jk
              by general-assoc auto
          equals (ω j ^ 2 • H jk) • ω j ^ 8 • (ω j • ω k ^ 7 • X jk)
              by right left axiom [1]
          equals (ω j ^ 2 • H jk) • ε • (ω j • ω k ^ 7 • X jk)
              by general-assoc auto
          equals ω j ^ 2 • H jk • ω j • ω k ^ 7 • X jk
    where
      comm : Greylyn.Rel ⊢ ω j • ω k === ω k • ω j
      comm = axiom ([4] {jk = lemma-less jk})

  open Inverse-Greylyn

  -- This lemma essentially states that XH = HZ, using the 1- and
  -- 2-level generators.
  lemma-Xjk-Hjk : ∀ {j} {k} {jk : Less j k} -> Greylyn.Rel ⊢ X jk • H jk === H jk • ω k ^ 4
  lemma-Xjk-Hjk {j} {k} {jk} =
      equational X jk • H jk
              by general-assoc auto
          equals ε • (X jk • H jk)
              by left axiom [2] reversed
          equals (H jk • H jk) • (X jk • H jk)
              by general-assoc auto
          equals H jk • (H jk • X jk) • H jk
              by right left axiom [18]
          equals H jk • (ω k ^ 4 • H jk) • H jk
              by general-assoc auto
          equals (H jk • ω k ^ 4) • (H jk • H jk)
              by right axiom [2]
          equals (H jk • ω k ^ 4) • ε
              by general-assoc auto
          equals H jk • ω k ^ 4

  -- ----------------------------------------------------------------------
  -- * The rewrite system for Greylyn's relations.

  -- We define a rewrite system. The basic idea is to reduce the
  -- number of H-generators as much as possible, and otherwise to move
  -- them as far as possible to the left. The details don't matter
  -- that much, as long as the rewrite system "works", i.e., it is
  -- sound (which is proved here) and it proves all the relations we
  -- need (in Soundness.agda).

  step : Step-Function Greylyn.Generator Greylyn.Rel
  
  step (ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₀₁ ∷ t) = just (H-gen ₀₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-ωk-ωk-ωk-ωk-Hjk)
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₀₂ ∷ t) = just (H-gen ₀₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-ωk-ωk-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₀₃ ∷ t) = just (H-gen ₀₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-ωk-ωk-ωk-ωk-Hjk)
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₁₂ ∷ t) = just (H-gen ₁₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-ωk-ωk-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₁₃ ∷ t) = just (H-gen ₁₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-ωk-ωk-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₂₃ ∷ t) = just (H-gen ₂₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-ωk-ωk-ωk-ωk-Hjk)

  step (ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₀₁ ∷ t) = just (ω-gen ₀ ∷ H-gen ₀₁ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-ωk-ωk-ωk-Hjk)
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₀₂ ∷ t) = just (ω-gen ₀ ∷ H-gen ₀₂ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-ωk-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₀₃ ∷ t) = just (ω-gen ₀ ∷ H-gen ₀₃ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-ωk-ωk-ωk-Hjk)
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₁₂ ∷ t) = just (ω-gen ₁ ∷ H-gen ₁₂ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-ωk-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₁₃ ∷ t) = just (ω-gen ₁ ∷ H-gen ₁₃ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-ωk-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₂₃ ∷ t) = just (ω-gen ₂ ∷ H-gen ₂₃ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-ωk-ωk-ωk-Hjk)
  
  step (ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₀₁ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₁ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-ωk-ωk-Hjk)
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₀₂ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₂ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₀₃ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₃ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-ωk-ωk-Hjk)
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₁₂ ∷ t) = just (ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₂ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₁₃ ∷ t) = just (ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₃ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-ωk-ωk-Hjk)
  step (ω-gen ₃ ∷ ω-gen ₃ ∷ H-gen ₂₃ ∷ t) = just (ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₂₃ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-ωk-ωk-Hjk)
  
  step (ω-gen ₁ ∷ H-gen ₀₁ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₁ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-ωk-Hjk)
  step (ω-gen ₂ ∷ H-gen ₀₂ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₂ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-ωk-Hjk)
  step (ω-gen ₃ ∷ H-gen ₀₃ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₃ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-ωk-Hjk)
  step (ω-gen ₂ ∷ H-gen ₁₂ ∷ t) = just (ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₂ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-ωk-Hjk)
  step (ω-gen ₃ ∷ H-gen ₁₃ ∷ t) = just (ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₃ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-ωk-Hjk)
  step (ω-gen ₃ ∷ H-gen ₂₃ ∷ t) = just (ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₂₃ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-ωk-Hjk)
  
  step (ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₁ ∷ t) = just (H-gen ₀₁ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-ωj-ωj-ωj-ωj-Hjk)
  step (ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₂ ∷ t) = just (H-gen ₀₂ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-ωj-ωj-ωj-ωj-Hjk)
  step (ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₃ ∷ t) = just (H-gen ₀₃ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-ωj-ωj-ωj-ωj-Hjk)
  step (ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₂ ∷ t) = just (H-gen ₁₂ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-ωj-ωj-ωj-ωj-Hjk)
  step (ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₃ ∷ t) = just (H-gen ₁₃ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-ωj-ωj-ωj-ωj-Hjk)
  step (ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₂₃ ∷ t) = just (H-gen ₂₃ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-ωj-ωj-ωj-ωj-Hjk)

  step (H-gen ₀₁ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₁ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₁ ∷ ω-gen ₀ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head lemma-Hjk-ωj-ωj-Hjk)
  step (H-gen ₀₂ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₂ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₂ ∷ ω-gen ₀ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head lemma-Hjk-ωj-ωj-Hjk)
  step (H-gen ₀₃ ∷ ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₃ ∷ t) = just (ω-gen ₀ ∷ ω-gen ₀ ∷ H-gen ₀₃ ∷ ω-gen ₀ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head lemma-Hjk-ωj-ωj-Hjk)
  step (H-gen ₁₂ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₂ ∷ t) = just (ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₂ ∷ ω-gen ₁ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head lemma-Hjk-ωj-ωj-Hjk)
  step (H-gen ₁₃ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₃ ∷ t) = just (ω-gen ₁ ∷ ω-gen ₁ ∷ H-gen ₁₃ ∷ ω-gen ₁ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head lemma-Hjk-ωj-ωj-Hjk)
  step (H-gen ₂₃ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₂₃ ∷ t) = just (ω-gen ₂ ∷ ω-gen ₂ ∷ H-gen ₂₃ ∷ ω-gen ₂ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head lemma-Hjk-ωj-ωj-Hjk)

  step (X-gen ₀₁ ∷ ω-gen ₀ ∷ t) = just (ω-gen ₁ ∷ X-gen ₀₁ ∷ t , at-head (axiom [11]))
  step (X-gen ₀₂ ∷ ω-gen ₀ ∷ t) = just (ω-gen ₂ ∷ X-gen ₀₂ ∷ t , at-head (axiom [11]))
  step (X-gen ₀₃ ∷ ω-gen ₀ ∷ t) = just (ω-gen ₃ ∷ X-gen ₀₃ ∷ t , at-head (axiom [11]))
  step (X-gen ₁₂ ∷ ω-gen ₁ ∷ t) = just (ω-gen ₂ ∷ X-gen ₁₂ ∷ t , at-head (axiom [11]))
  step (X-gen ₁₃ ∷ ω-gen ₁ ∷ t) = just (ω-gen ₃ ∷ X-gen ₁₃ ∷ t , at-head (axiom [11]))
  step (X-gen ₂₃ ∷ ω-gen ₂ ∷ t) = just (ω-gen ₃ ∷ X-gen ₂₃ ∷ t , at-head (axiom [11]))

  step (X-gen ₀₁ ∷ ω-gen ₁ ∷ t) = just (ω-gen ₀ ∷ X-gen ₀₁ ∷ t , at-head (axiom [10]))
  step (X-gen ₀₂ ∷ ω-gen ₂ ∷ t) = just (ω-gen ₀ ∷ X-gen ₀₂ ∷ t , at-head (axiom [10]))
  step (X-gen ₀₃ ∷ ω-gen ₃ ∷ t) = just (ω-gen ₀ ∷ X-gen ₀₃ ∷ t , at-head (axiom [10]))
  step (X-gen ₁₂ ∷ ω-gen ₂ ∷ t) = just (ω-gen ₁ ∷ X-gen ₁₂ ∷ t , at-head (axiom [10]))
  step (X-gen ₁₃ ∷ ω-gen ₃ ∷ t) = just (ω-gen ₁ ∷ X-gen ₁₃ ∷ t , at-head (axiom [10]))
  step (X-gen ₂₃ ∷ ω-gen ₃ ∷ t) = just (ω-gen ₂ ∷ X-gen ₂₃ ∷ t , at-head (axiom [10]))
  
  step (X-gen ₀₁ ∷ H-gen ₀₁ ∷ t) = just (H-gen ₀₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ ω-gen ₁ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₂ ∷ H-gen ₀₂ ∷ t) = just (H-gen ₀₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₀₃ ∷ H-gen ₀₃ ∷ t) = just (H-gen ₀₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₂ ∷ H-gen ₁₂ ∷ t) = just (H-gen ₁₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ ω-gen ₂ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₁₃ ∷ H-gen ₁₃ ∷ t) = just (H-gen ₁₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ t , at-head lemma-Xjk-Hjk)
  step (X-gen ₂₃ ∷ H-gen ₂₃ ∷ t) = just (H-gen ₂₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ ω-gen ₃ ∷ t , at-head lemma-Xjk-Hjk)
  
  -- Catch-all
  step _ = nothing

-- Finally, we instantiate the Step-With-Standardization module with
-- the two rewrite relations defined above, to obtain a tactic
-- 'rewrite-twolevel'.

module Greylyn-Rewrite-Twolevel = Step-With-Standardization (step-cong Greylyn-Step-Order.step then step-cong Greylyn-Step-Twolevel.step) Commuting-Greylyn.comm-canonical Commuting-Greylyn.lemma-comm-canonical renaming (general-rewrite to rewrite-twolevel)
