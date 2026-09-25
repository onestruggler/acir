------------------------------------------------------------------------
-- Presentations of groups
--
-- Greylyn-Simplified: a smaller presentation of U₄(ℤ[1/√2,i]), with the
-- five generators ω₀, X₀₁, X₁₂, X₂₃, H₀₁ and 19 relations, equivalent to
-- Greylyn's (16 generators, 123 relations with their indices), by the
-- simplified Reidemeister-Schreier theorem.  Ported from the Agda code
-- accompanying Bian and Selinger, "Generators and relations for 2-qubit
-- Clifford+T operators" (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Greylyn-Simplified where

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
open import Examples.Groups.Clifford+T-2qubit.Generator as GG
open import Presentation.Tactics.Reidemeister-Schreier

open Monoid-Equational
open Reidemeister-Schreier-Simplified

-- We refer to Greylyn's original generators and relations by the
-- qualified types G.Generator and G.Rel.
module G = GG.Greylyn  
open G hiding (Generator; Rel)

-- The new set of generators.
data Generator : Set where
  ω₀-gen : Generator
  X₀₁-gen : Generator
  X₁₂-gen : Generator
  X₂₃-gen : Generator
  H₀₁-gen : Generator

-- For convenience, we define a singleton word for each new
-- generator, as well as for all of Greylyn's original generators.
-- This makes the relations easier to state.
X₀₁ : Word Generator
X₀₁ = [ X₀₁-gen ]ʷ

X₁₂ : Word Generator
X₁₂ = [ X₁₂-gen ]ʷ

X₂₃ : Word Generator
X₂₃ = [ X₂₃-gen ]ʷ

X₀₂ : Word Generator
X₀₂ = X₁₂ • X₀₁ • X₁₂

X₀₃ : Word Generator
X₀₃ = X₂₃ • X₀₂ • X₂₃

X₁₃ : Word Generator
X₁₃ = X₂₃ • X₁₂ • X₂₃

ω₀ : Word Generator
ω₀ = [ ω₀-gen ]ʷ

ω₁ : Word Generator
ω₁ = X₀₁ • ω₀ • X₀₁

ω₂ : Word Generator
ω₂ = X₁₂ • ω₁ • X₁₂

ω₃ : Word Generator
ω₃ = X₂₃ • ω₂ • X₂₃

H₀₁ : Word Generator
H₀₁ = [ H₀₁-gen ]ʷ

H₀₂ : Word Generator
H₀₂ = X₁₂ • H₀₁ • X₁₂

H₀₃ : Word Generator
H₀₃ = X₂₃ • H₀₂ • X₂₃

H₁₂ : Word Generator
H₁₂ = X₀₁ • X₁₂ • H₀₁ • X₁₂ • X₀₁

H₁₃ : Word Generator
H₁₃ = X₂₃ • H₁₂ • X₂₃

H₂₃ : Word Generator
H₂₃ = X₁₂ • X₂₃ • H₁₂ • X₂₃ • X₁₂

-- The new set of relations.
data Rel : Context Generator where
  [S1] : ω₀ ^ 8 === ε ∈ Rel
  [S2] : H₀₁ ^ 2 === ε ∈ Rel
  [S3] : X₀₁ ^ 2 === ε ∈ Rel
  [S4] : X₁₂ ^ 2 === ε ∈ Rel
  [S5] : X₂₃ ^ 2 === ε ∈ Rel

  [S6] : ω₀ • ω₁ === ω₁ • ω₀ ∈ Rel
  [S7] : ω₂ • H₀₁ === H₀₁ • ω₂ ∈ Rel
  [S8] : ω₀ • X₁₂ === X₁₂ • ω₀ ∈ Rel
  [S9] : ω₀ • X₂₃ === X₂₃ • ω₀ ∈ Rel
  [S10] : H₀₁ • H₂₃ === H₂₃ • H₀₁ ∈ Rel
  [S11] : H₀₁ • X₂₃ === X₂₃ • H₀₁ ∈ Rel
  [S12] : X₀₁ • X₂₃ === X₂₃ • X₀₁ ∈ Rel

  [S13] : X₀₁ • X₁₂ • X₀₁ === X₁₂ • X₀₁ • X₁₂ ∈ Rel
  [S14] : X₁₂ • X₂₃ • X₁₂ === X₂₃ • X₁₂ • X₂₃ ∈ Rel

  [S15] : ω₀ • ω₁ • X₀₁ === X₀₁ • ω₀ • ω₁ ∈ Rel
  [S16] : ω₀ • ω₁ • H₀₁ === H₀₁ • ω₀ • ω₁ ∈ Rel

  [S17] : H₀₁ • X₀₁ === ω₁ ^ 4 • H₀₁ ∈ Rel
  [S18] : H₀₁ • ω₀ ^ 2 • H₀₁ === ω₀ ^ 6 • H₀₁ • ω₀ ^ 3 • ω₁ ^ 5 ∈ Rel
  [S19] : H₀₁ • H₂₃ • H₀₂ • H₁₃ === H₀₂ • H₁₃ • H₀₁ • H₂₃ ∈ Rel

-- ----------------------------------------------------------------------
-- * Tactics

module Greylyn-Simplified-Step where
  open Rewriting
  open InContext
  open Associative

  -- We define a rewrite system for simplifying words in the new
  -- generators. This takes care of a few things such as commuting
  -- generators, simplifying permutations made of Xⱼₖ generators,
  -- and reducing powers of generators.

  step : Step-Function Generator Rel

  -- Topological rules:
  step (X₁₂-gen ∷ ω₀-gen ∷ t) = just (ω₀-gen ∷ X₁₂-gen ∷ t , at-head (axiom [S8] reversed))
  step (X₂₃-gen ∷ ω₀-gen ∷ t) = just (ω₀-gen ∷ X₂₃-gen ∷ t , at-head (axiom [S9] reversed))
  step (X₂₃-gen ∷ H₀₁-gen ∷ t) = just (H₀₁-gen ∷ X₂₃-gen ∷ t , at-head (axiom [S11] reversed))
  step (X₂₃-gen ∷ X₀₁-gen ∷ t) = just (X₀₁-gen ∷ X₂₃-gen ∷ t , at-head (axiom [S12] reversed))
  step (X₀₁-gen ∷ X₀₁-gen ∷ t) = just (t , at-head (axiom [S3]))
  step (X₁₂-gen ∷ X₁₂-gen ∷ t) = just (t , at-head (axiom [S4]))
  step (X₂₃-gen ∷ X₂₃-gen ∷ t) = just (t , at-head (axiom [S5]))
  step (X₀₁-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ t) = just (X₁₂-gen ∷ X₀₁-gen ∷ X₁₂-gen ∷ t , at-head (axiom [S13]))
  step (X₁₂-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ t) = just (X₂₃-gen ∷ X₁₂-gen ∷ X₂₃-gen ∷ t , at-head (axiom [S14]))
  step (X₀₁-gen ∷ X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ t) = just (X₂₃-gen ∷ X₁₂-gen ∷ X₀₁-gen ∷ X₁₂-gen ∷ t , at-head lemma)
    where
      lemma : Rel ⊢ X₀₁ • X₂₃ • X₁₂ • X₀₁ === X₂₃ • X₁₂ • X₀₁ • X₁₂
      lemma =
        equational X₀₁ • X₂₃ • X₁₂ • X₀₁
                by general-assoc auto
            equals (X₀₁ • X₂₃) • X₁₂ • X₀₁
                by left axiom [S12]
            equals (X₂₃ • X₀₁) • X₁₂ • X₀₁
                by general-assoc auto
            equals X₂₃ • (X₀₁ • X₁₂ • X₀₁)
                by right axiom [S13]
            equals X₂₃ • (X₁₂ • X₀₁ • X₁₂)
                by general-assoc auto
            equals X₂₃ • X₁₂ • X₀₁ • X₁₂

  -- Order of elements:
  step (ω₀-gen ∷ ω₀-gen ∷ ω₀-gen ∷ ω₀-gen ∷ ω₀-gen ∷ ω₀-gen ∷ ω₀-gen ∷ ω₀-gen ∷ t) = just (t , at-head (axiom [S1]))
  step (H₀₁-gen ∷ H₀₁-gen ∷ t) = just (t , at-head (axiom [S2]))

  step x = nothing

module Greylyn-Rewrite = Rewriting.Step (Rewriting.step-cong Greylyn-Simplified-Step.step)

open Greylyn-Rewrite
open Associative

-- The new generators also have a group structure.
group-like : Grouplike Rel
group-like ω₀-gen = (ω₀ ^ 7 , trans (general-assoc auto) (axiom [S1]))
group-like X₀₁-gen = (X₀₁ , axiom [S3])
group-like X₁₂-gen = (X₁₂ , axiom [S4])
group-like X₂₃-gen = (X₂₃ , axiom [S5])
group-like H₀₁-gen = (H₀₁ , axiom [S2])

open Inverse Generator Rel group-like

-- A simple tactic for proving an equation by doing a suitable basis
-- change (i.e., conjugating the equation by a given word g).
by-basis-change : ∀ {u v u' v'} -> (g : Word Generator) -> Rel ⊢ u === v -> (n : ℕ) -> (multistep n (list-of-word u') , multistep n (list-of-word (g • v • g ⁻¹))) ≡ (multistep n (list-of-word (g • u • g ⁻¹)) , multistep n (list-of-word v')) -> Rel ⊢ u' === v'
by-basis-change {u} {v} {u'} {v'} g hyp n x =
  equational u'
          by general-rewrite n (Eq.cong proj₁ x)
      equals g • u • g ⁻¹
          by right left hyp
      equals g • v • g ⁻¹
          by general-rewrite n (Eq.cong proj₂ x)
      equals v'

-- ----------------------------------------------------------------------
-- * Completeness of the new relations

-- Translation from the new to the old generators.
greylyn-of-simple-gen : Generator -> Word G.Generator
greylyn-of-simple-gen ω₀-gen = ω ₀
greylyn-of-simple-gen X₀₁-gen = X ₀₁
greylyn-of-simple-gen X₁₂-gen = X ₁₂
greylyn-of-simple-gen X₂₃-gen = X ₂₃
greylyn-of-simple-gen H₀₁-gen = H ₀₁

-- Translation of words.
greylyn-of-simple : Word Generator -> Word G.Generator
greylyn-of-simple = greylyn-of-simple-gen ʷ

-- Translation from the old to the new generators.
simple-of-greylyn-gen : G.Generator -> Word Generator
simple-of-greylyn-gen (ω-gen ₀) = ω₀
simple-of-greylyn-gen (ω-gen ₁) = ω₁
simple-of-greylyn-gen (ω-gen ₂) = ω₂
simple-of-greylyn-gen (ω-gen ₃) = ω₃
simple-of-greylyn-gen (X-gen ₀₁) = X₀₁
simple-of-greylyn-gen (X-gen ₀₂) = X₀₂
simple-of-greylyn-gen (X-gen ₀₃) = X₀₃
simple-of-greylyn-gen (X-gen ₁₂) = X₁₂
simple-of-greylyn-gen (X-gen ₁₃) = X₁₃
simple-of-greylyn-gen (X-gen ₂₃) = X₂₃
simple-of-greylyn-gen (H-gen ₀₁) = H₀₁
simple-of-greylyn-gen (H-gen ₀₂) = H₀₂
simple-of-greylyn-gen (H-gen ₀₃) = H₀₃
simple-of-greylyn-gen (H-gen ₁₂) = H₁₂
simple-of-greylyn-gen (H-gen ₁₃) = H₁₃
simple-of-greylyn-gen (H-gen ₂₃) = H₂₃

-- Translation of words.
simple-of-greylyn : Word G.Generator -> Word Generator
simple-of-greylyn = simple-of-greylyn-gen ʷ

-- The two sets of relations are equivalent, but it turns out that
-- we don't need to prove both directions of the equivalence. We
-- only need that every equation that follows from Greylyn's
-- original relations also follows from the simplified relations.
-- This is the content of theorem-greylyn-of-simple and
-- theorem-simple-of-greylyn below. We prove them using the
-- simplified Reidemeister-Schreier theorem.

module Greylyn-Simplified-Proofs where

  -- The first hypothesis of the Reidemeister-Schreier theorem is
  -- that the translation from the simple generators to the original
  -- generators and back is the identity. It is trivial in the
  -- current situation.
  hypA : ∀ (x : Generator) -> Rel ⊢ [ x ]ʷ === simple-of-greylyn (greylyn-of-simple-gen x)
  hypA ω₀-gen = refl
  hypA X₀₁-gen = refl
  hypA X₁₂-gen = refl
  hypA X₂₃-gen = refl
  hypA H₀₁-gen = refl

  -- The second hypothesis of the Reidemeister-Schreier theorem is
  -- that each of Greylyn's 123 relations follows from the new
  -- simplified relations. We prove this by a case distinction with
  -- 123 cases. All of the cases can either be solved by the above
  -- rewrite system or by rewriting after a suitable basis change.
  hypB : ∀ (u t : Word G.Generator) -> u === t ∈ G.Rel -> Rel ⊢ simple-of-greylyn u === simple-of-greylyn t
  hypB _ _ ([1] {₀}) = general-rewrite 10 auto
  hypB _ _ ([1] {₁}) = general-rewrite 10 auto
  hypB _ _ ([1] {₂}) = general-rewrite 20 auto
  hypB _ _ ([1] {₃}) = general-rewrite 30 auto
  hypB _ _ ([2] {jk = ₀₁}) = general-rewrite 10 auto
  hypB _ _ ([2] {jk = ₀₂}) = general-rewrite 10 auto
  hypB _ _ ([2] {jk = ₀₃}) = general-rewrite 10 auto
  hypB _ _ ([2] {jk = ₁₂}) = general-rewrite 10 auto
  hypB _ _ ([2] {jk = ₁₃}) = general-rewrite 10 auto
  hypB _ _ ([2] {jk = ₂₃}) = general-rewrite 20 auto
  hypB _ _ ([3] {jk = ₀₁}) = general-rewrite 10 auto
  hypB _ _ ([3] {jk = ₀₂}) = general-rewrite 10 auto
  hypB _ _ ([3] {jk = ₀₃}) = general-rewrite 10 auto
  hypB _ _ ([3] {jk = ₁₂}) = general-rewrite 10 auto
  hypB _ _ ([3] {jk = ₁₃}) = general-rewrite 10 auto
  hypB _ _ ([3] {jk = ₂₃}) = general-rewrite 10 auto
  hypB _ _ ([4] {jk = ₀₁}) = axiom [S6]
  hypB _ _ ([4] {jk = ₀₂}) = by-basis-change X₁₂ (axiom [S6]) 10 auto
  hypB _ _ ([4] {jk = ₀₃}) = by-basis-change X₁₃ (axiom [S6]) 10 auto
  hypB _ _ ([4] {jk = ₁₀}) = axiom [S6] reversed
  hypB _ _ ([4] {jk = ₁₂}) = by-basis-change X₀₂ (axiom [S6]) 10 auto reversed
  hypB _ _ ([4] {jk = ₁₃}) = by-basis-change X₀₃ (axiom [S6]) 10 auto reversed
  hypB _ _ ([4] {jk = ₂₀}) = by-basis-change X₁₂ (axiom [S6]) 10 auto reversed
  hypB _ _ ([4] {jk = ₂₁}) = by-basis-change X₀₂ (axiom [S6]) 10 auto
  hypB _ _ ([4] {jk = ₂₃}) = by-basis-change (X₀₂ • X₁₃) (axiom [S6]) 10 auto
  hypB _ _ ([4] {jk = ₃₀}) = by-basis-change X₁₃ (axiom [S6]) 10 auto reversed
  hypB _ _ ([4] {jk = ₃₁}) = by-basis-change X₀₃ (axiom [S6]) 10 auto
  hypB _ _ ([4] {jk = ₃₂}) = by-basis-change (X₀₂ • X₁₃) (axiom [S6]) 10 auto reversed
  hypB _ _ ([5] {jk = ₀₁} {₁₀} {()})
  hypB _ _ ([5] {jk = ₀₁} {₂₀} {₂₁}) = axiom [S7]
  hypB _ _ ([5] {jk = ₀₁} {₃₀} {₃₁}) = by-basis-change X₂₃ (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₀₂} {₁₀} {₁₂}) = by-basis-change X₁₂ (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₀₂} {₂₀} {()})
  hypB _ _ ([5] {jk = ₀₂} {₃₀} {₃₂}) = by-basis-change (X₁₂ • X₂₃) (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₀₃} {₁₀} {₁₃}) = by-basis-change (X₂₃ • X₁₂) (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₀₃} {₂₀} {₂₃}) = by-basis-change X₁₃ (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₀₃} {₃₀} {()})
  hypB _ _ ([5] {jk = ₁₂} {₀₁} {₀₂}) = by-basis-change (X₀₁ • X₁₂) (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₁₂} {₂₁} {()})
  hypB _ _ ([5] {jk = ₁₂} {₃₁} {₃₂}) = by-basis-change (X₀₁ • X₁₂ • X₂₃) (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₁₃} {₀₁} {₀₃}) = by-basis-change (X₀₁ • X₂₃ • X₁₂) (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₁₃} {₂₁} {₂₃}) = by-basis-change (X₀₁ • X₁₃) (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₁₃} {₃₁} {()})
  hypB _ _ ([5] {jk = ₂₃} {₀₂} {₀₃}) = by-basis-change (X₀₂ • X₁₃) (axiom [S7]) 20 auto
  hypB _ _ ([5] {jk = ₂₃} {₁₂} {₁₃}) = by-basis-change (X₁₂ • X₀₁ • X₁₃) (axiom [S7]) 10 auto
  hypB _ _ ([5] {jk = ₂₃} {₃₂} {()})
  hypB _ _ ([6] {jk = ₀₁} {₁₀} {()})
  hypB _ _ ([6] {jk = ₀₁} {₂₀} {₂₁}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₀₁} {₃₀} {₃₁}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₀₂} {₁₀} {₁₂}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₀₂} {₂₀} {()})
  hypB _ _ ([6] {jk = ₀₂} {₃₀} {₃₂}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₀₃} {₁₀} {₁₃}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₀₃} {₂₀} {₂₃}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₀₃} {₃₀} {()})
  hypB _ _ ([6] {jk = ₁₂} {₀₁} {₀₂}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₁₂} {₂₁} {()})
  hypB _ _ ([6] {jk = ₁₂} {₃₁} {₃₂}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₁₃} {₀₁} {₀₃}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₁₃} {₂₁} {₂₃}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₁₃} {₃₁} {()})
  hypB _ _ ([6] {jk = ₂₃} {₀₂} {₀₃}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₂₃} {₁₂} {₁₃}) = general-rewrite 10 auto
  hypB _ _ ([6] {jk = ₂₃} {₃₂} {()})
  hypB _ _ ([7] {jk = ₀₁} {₀₁} {lj = ()})
  hypB _ _ ([7] {jk = ₀₁} {₀₂} {lj = ()})
  hypB _ _ ([7] {jk = ₀₁} {₀₃} {lj = ()})
  hypB _ _ ([7] {jk = ₀₁} {₁₂} {lk = ()})
  hypB _ _ ([7] {jk = ₀₁} {₁₃} {lk = ()})
  hypB _ _ ([7] {jk = ₀₁} {₂₃} {₂₀} {₂₁} {₃₀} {₃₁}) = axiom [S10]
  hypB _ _ ([7] {jk = ₀₂} {₀₁} {lj = ()})
  hypB _ _ ([7] {jk = ₀₂} {₀₂} {lj = ()})
  hypB _ _ ([7] {jk = ₀₂} {₀₃} {lj = ()})
  hypB _ _ ([7] {jk = ₀₂} {₁₂} {tk = ()})
  hypB _ _ ([7] {jk = ₀₂} {₁₃} {₁₀} {₁₂} {₃₀} {₃₂}) = by-basis-change X₁₂ (axiom [S10]) 10 auto
  hypB _ _ ([7] {jk = ₀₂} {₂₃} {lk = ()})
  hypB _ _ ([7] {jk = ₀₃} {₀₁} {lj = ()})
  hypB _ _ ([7] {jk = ₀₃} {₀₂} {lj = ()})
  hypB _ _ ([7] {jk = ₀₃} {₀₃} {lj = ()})
  hypB _ _ ([7] {jk = ₀₃} {₁₂} {₁₀} {₁₃} {₂₀} {₂₃}) = by-basis-change (X₂₃ • X₁₂) (axiom [S10]) 10 auto
  hypB _ _ ([7] {jk = ₀₃} {₁₃} {tk = ()})
  hypB _ _ ([7] {jk = ₀₃} {₂₃} {tk = ()})
  hypB _ _ ([7] {jk = ₁₂} {₀₁} {tj = ()})
  hypB _ _ ([7] {jk = ₁₂} {₀₂} {tk = ()})
  hypB _ _ ([7] {jk = ₁₂} {₀₃} {₀₁} {₀₂} {₃₁} {₃₂}) = by-basis-change (X₀₁ • X₁₂) (axiom [S10]) 10 auto
  hypB _ _ ([7] {jk = ₁₂} {₁₂} {tk = ()})
  hypB _ _ ([7] {jk = ₁₂} {₁₃} {lj = ()})
  hypB _ _ ([7] {jk = ₁₂} {₂₃} {lk = ()})
  hypB _ _ ([7] {jk = ₁₃} {₀₁} {tj = ()})
  hypB _ _ ([7] {jk = ₁₃} {₀₂} {₀₁} {₀₃} {₂₁} {₂₃}) = by-basis-change (X₀₁ • X₂₃ • X₁₂) (axiom [S10]) 10 auto
  hypB _ _ ([7] {jk = ₁₃} {₀₃} {tk = ()})
  hypB _ _ ([7] {jk = ₁₃} {₁₂} {lj = ()})
  hypB _ _ ([7] {jk = ₁₃} {₁₃} {lj = ()})
  hypB _ _ ([7] {jk = ₁₃} {₂₃} {tk = ()})
  hypB _ _ ([7] {jk = ₂₃} {₀₁} {₀₂} {₀₃} {₁₂} {₁₃}) = axiom [S10] reversed
  hypB _ _ ([7] {jk = ₂₃} {₀₂} {tj = ()})
  hypB _ _ ([7] {jk = ₂₃} {₀₃} {tk = ()})
  hypB _ _ ([7] {jk = ₂₃} {₁₂} {tj = ()})
  hypB _ _ ([7] {jk = ₂₃} {₁₃} {tk = ()})
  hypB _ _ ([7] {jk = ₂₃} {₂₃} {tk = ()})
  hypB _ _ ([8] {jk = ₀₁} {₀₁} {lj = ()})
  hypB _ _ ([8] {jk = ₀₁} {₀₂} {lj = ()})
  hypB _ _ ([8] {jk = ₀₁} {₀₃} {lj = ()})
  hypB _ _ ([8] {jk = ₀₁} {₁₂} {lk = ()})
  hypB _ _ ([8] {jk = ₀₁} {₁₃} {lk = ()})
  hypB _ _ ([8] {jk = ₀₁} {₂₃} {₂₀} {₂₁} {₃₀} {₃₁}) = general-rewrite 10 auto
  hypB _ _ ([8] {jk = ₀₂} {₀₁} {lj = ()})
  hypB _ _ ([8] {jk = ₀₂} {₀₂} {lj = ()})
  hypB _ _ ([8] {jk = ₀₂} {₀₃} {lj = ()})
  hypB _ _ ([8] {jk = ₀₂} {₁₂} {tk = ()})
  hypB _ _ ([8] {jk = ₀₂} {₁₃} {₁₀} {₁₂} {₃₀} {₃₂}) = general-rewrite 10 auto 
  hypB _ _ ([8] {jk = ₀₂} {₂₃} {lk = ()})
  hypB _ _ ([8] {jk = ₀₃} {₀₁} {lj = ()})
  hypB _ _ ([8] {jk = ₀₃} {₀₂} {lj = ()})
  hypB _ _ ([8] {jk = ₀₃} {₀₃} {lj = ()})
  hypB _ _ ([8] {jk = ₀₃} {₁₂} {₁₀} {₁₃} {₂₀} {₂₃}) = general-rewrite 10 auto 
  hypB _ _ ([8] {jk = ₀₃} {₁₃} {tk = ()})
  hypB _ _ ([8] {jk = ₀₃} {₂₃} {tk = ()})
  hypB _ _ ([8] {jk = ₁₂} {₀₁} {tj = ()})
  hypB _ _ ([8] {jk = ₁₂} {₀₂} {tk = ()})
  hypB _ _ ([8] {jk = ₁₂} {₀₃} {₀₁} {₀₂} {₃₁} {₃₂}) = general-rewrite 10 auto 
  hypB _ _ ([8] {jk = ₁₂} {₁₂} {tk = ()})
  hypB _ _ ([8] {jk = ₁₂} {₁₃} {lj = ()})
  hypB _ _ ([8] {jk = ₁₂} {₂₃} {lk = ()})
  hypB _ _ ([8] {jk = ₁₃} {₀₁} {tj = ()})
  hypB _ _ ([8] {jk = ₁₃} {₀₂} {₀₁} {₀₃} {₂₁} {₂₃}) = general-rewrite 10 auto 
  hypB _ _ ([8] {jk = ₁₃} {₀₃} {tk = ()})
  hypB _ _ ([8] {jk = ₁₃} {₁₂} {lj = ()})
  hypB _ _ ([8] {jk = ₁₃} {₁₃} {lj = ()})
  hypB _ _ ([8] {jk = ₁₃} {₂₃} {tk = ()})
  hypB _ _ ([8] {jk = ₂₃} {₀₁} {₀₂} {₀₃} {₁₂} {₁₃}) = general-rewrite 10 auto 
  hypB _ _ ([8] {jk = ₂₃} {₀₂} {tj = ()})
  hypB _ _ ([8] {jk = ₂₃} {₀₃} {tk = ()})
  hypB _ _ ([8] {jk = ₂₃} {₁₂} {tj = ()})
  hypB _ _ ([8] {jk = ₂₃} {₁₃} {tk = ()})
  hypB _ _ ([8] {jk = ₂₃} {₂₃} {tk = ()})
  hypB _ _ ([9] {jk = ₀₁} {₀₁} {lj = ()})
  hypB _ _ ([9] {jk = ₀₁} {₀₂} {lj = ()})
  hypB _ _ ([9] {jk = ₀₁} {₀₃} {lj = ()})
  hypB _ _ ([9] {jk = ₀₁} {₁₂} {lk = ()})
  hypB _ _ ([9] {jk = ₀₁} {₁₃} {lk = ()})
  hypB _ _ ([9] {jk = ₀₁} {₂₃} {₂₀} {₂₁} {₃₀} {₃₁}) = general-rewrite 10 auto
  hypB _ _ ([9] {jk = ₀₂} {₀₁} {lj = ()})
  hypB _ _ ([9] {jk = ₀₂} {₀₂} {lj = ()})
  hypB _ _ ([9] {jk = ₀₂} {₀₃} {lj = ()})
  hypB _ _ ([9] {jk = ₀₂} {₁₂} {tk = ()})
  hypB _ _ ([9] {jk = ₀₂} {₁₃} {₁₀} {₁₂} {₃₀} {₃₂}) = general-rewrite 10 auto 
  hypB _ _ ([9] {jk = ₀₂} {₂₃} {lk = ()})
  hypB _ _ ([9] {jk = ₀₃} {₀₁} {lj = ()})
  hypB _ _ ([9] {jk = ₀₃} {₀₂} {lj = ()})
  hypB _ _ ([9] {jk = ₀₃} {₀₃} {lj = ()})
  hypB _ _ ([9] {jk = ₀₃} {₁₂} {₁₀} {₁₃} {₂₀} {₂₃}) = general-rewrite 10 auto 
  hypB _ _ ([9] {jk = ₀₃} {₁₃} {tk = ()})
  hypB _ _ ([9] {jk = ₀₃} {₂₃} {tk = ()})
  hypB _ _ ([9] {jk = ₁₂} {₀₁} {tj = ()})
  hypB _ _ ([9] {jk = ₁₂} {₀₂} {tk = ()})
  hypB _ _ ([9] {jk = ₁₂} {₀₃} {₀₁} {₀₂} {₃₁} {₃₂}) = general-rewrite 10 auto 
  hypB _ _ ([9] {jk = ₁₂} {₁₂} {tk = ()})
  hypB _ _ ([9] {jk = ₁₂} {₁₃} {lj = ()})
  hypB _ _ ([9] {jk = ₁₂} {₂₃} {lk = ()})
  hypB _ _ ([9] {jk = ₁₃} {₀₁} {tj = ()})
  hypB _ _ ([9] {jk = ₁₃} {₀₂} {₀₁} {₀₃} {₂₁} {₂₃}) = general-rewrite 10 auto 
  hypB _ _ ([9] {jk = ₁₃} {₀₃} {tk = ()})
  hypB _ _ ([9] {jk = ₁₃} {₁₂} {lj = ()})
  hypB _ _ ([9] {jk = ₁₃} {₁₃} {lj = ()})
  hypB _ _ ([9] {jk = ₁₃} {₂₃} {tk = ()})
  hypB _ _ ([9] {jk = ₂₃} {₀₁} {₀₂} {₀₃} {₁₂} {₁₃}) = general-rewrite 10 auto 
  hypB _ _ ([9] {jk = ₂₃} {₀₂} {tj = ()})
  hypB _ _ ([9] {jk = ₂₃} {₀₃} {tk = ()})
  hypB _ _ ([9] {jk = ₂₃} {₁₂} {tj = ()})
  hypB _ _ ([9] {jk = ₂₃} {₁₃} {tk = ()})
  hypB _ _ ([9] {jk = ₂₃} {₂₃} {tk = ()})
  hypB _ _ ([10] {jk = ₀₁}) = general-rewrite 10 auto
  hypB _ _ ([10] {jk = ₀₂}) = general-rewrite 10 auto
  hypB _ _ ([10] {jk = ₀₃}) = general-rewrite 10 auto
  hypB _ _ ([10] {jk = ₁₂}) = general-rewrite 10 auto
  hypB _ _ ([10] {jk = ₁₃}) = general-rewrite 10 auto
  hypB _ _ ([10] {jk = ₂₃}) = general-rewrite 10 auto
  hypB _ _ ([11] {jk = ₀₁}) = general-rewrite 10 auto
  hypB _ _ ([11] {jk = ₀₂}) = general-rewrite 10 auto
  hypB _ _ ([11] {jk = ₀₃}) = general-rewrite 10 auto
  hypB _ _ ([11] {jk = ₁₂}) = general-rewrite 10 auto
  hypB _ _ ([11] {jk = ₁₃}) = general-rewrite 10 auto
  hypB _ _ ([11] {jk = ₂₃}) = general-rewrite 10 auto
  hypB _ _ ([12] {jk = ₀₁} {₁₂} {₀₂}) = general-rewrite 10 auto
  hypB _ _ ([12] {jk = ₀₁} {₁₃} {₀₃}) = general-rewrite 10 auto
  hypB _ _ ([12] {jk = ₀₂} {₂₃} {₀₃}) = general-rewrite 10 auto
  hypB _ _ ([12] {jk = ₀₃} {kl = ()})
  hypB _ _ ([12] {jk = ₁₂} {₂₃} {₁₃}) = general-rewrite 10 auto
  hypB _ _ ([12] {jk = ₁₃} {kl = ()})
  hypB _ _ ([12] {jk = ₂₃} {kl = ()})
  hypB _ _ ([13] {jk = ₀₁} {lj = ()})
  hypB _ _ ([13] {jk = ₀₂} {lj = ()})
  hypB _ _ ([13] {jk = ₀₃} {lj = ()})
  hypB _ _ ([13] {jk = ₁₂} {₀₂} {₀₁}) = general-rewrite 10 auto
  hypB _ _ ([13] {jk = ₁₃} {₀₃} {₀₁}) = general-rewrite 10 auto
  hypB _ _ ([13] {jk = ₂₃} {₀₃} {₀₂}) = general-rewrite 10 auto
  hypB _ _ ([13] {jk = ₂₃} {₁₃} {₁₂}) = general-rewrite 10 auto
  hypB _ _ ([14] {jk = ₀₁} {₁₂} {₀₂}) = general-rewrite 10 auto
  hypB _ _ ([14] {jk = ₀₁} {₁₃} {₀₃}) = general-rewrite 10 auto
  hypB _ _ ([14] {jk = ₀₂} {₂₃} {₀₃}) = general-rewrite 10 auto
  hypB _ _ ([14] {jk = ₀₃} {kl = ()})
  hypB _ _ ([14] {jk = ₁₂} {₂₃} {₁₃}) = general-rewrite 10 auto
  hypB _ _ ([14] {jk = ₁₃} {kl = ()})
  hypB _ _ ([14] {jk = ₂₃} {kl = ()})
  hypB _ _ ([15] {jk = ₀₁} {lj = ()})
  hypB _ _ ([15] {jk = ₀₂} {lj = ()})
  hypB _ _ ([15] {jk = ₀₃} {lj = ()})
  hypB _ _ ([15] {jk = ₁₂} {₀₂} {₀₁}) = general-rewrite 10 auto
  hypB _ _ ([15] {jk = ₁₃} {₀₃} {₀₁}) = general-rewrite 10 auto
  hypB _ _ ([15] {jk = ₂₃} {₀₃} {₀₂}) = general-rewrite 10 auto
  hypB _ _ ([15] {jk = ₂₃} {₁₃} {₁₂}) = general-rewrite 10 auto
  hypB _ _ ([16] {jk = ₀₁}) = axiom [S15]
  hypB _ _ ([16] {jk = ₀₂}) = by-basis-change X₁₂ (axiom [S15]) 10 auto
  hypB _ _ ([16] {jk = ₀₃}) = by-basis-change X₁₃ (axiom [S15]) 10 auto
  hypB _ _ ([16] {jk = ₁₂}) = by-basis-change (X₀₁ • X₁₂) (axiom [S15]) 10 auto
  hypB _ _ ([16] {jk = ₁₃}) = by-basis-change (X₀₁ • X₁₃) (axiom [S15]) 10 auto
  hypB _ _ ([16] {jk = ₂₃}) = by-basis-change (X₀₂ • X₁₃) (axiom [S15]) 20 auto
  hypB _ _ ([17] {jk = ₀₁}) = axiom [S16]
  hypB _ _ ([17] {jk = ₀₂}) = by-basis-change X₁₂ (axiom [S16]) 10 auto
  hypB _ _ ([17] {jk = ₀₃}) = by-basis-change X₁₃ (axiom [S16]) 10 auto
  hypB _ _ ([17] {jk = ₁₂}) = by-basis-change (X₀₁ • X₁₂) (axiom [S16]) 10 auto
  hypB _ _ ([17] {jk = ₁₃}) = by-basis-change (X₀₁ • X₁₃) (axiom [S16]) 10 auto
  hypB _ _ ([17] {jk = ₂₃}) = by-basis-change (X₀₂ • X₁₃) (axiom [S16]) 20 auto
  hypB _ _ ([18] {jk = ₀₁}) = axiom [S17]
  hypB _ _ ([18] {jk = ₀₂}) = by-basis-change X₁₂ (axiom [S17]) 10 auto
  hypB _ _ ([18] {jk = ₀₃}) = by-basis-change X₁₃ (axiom [S17]) 20 auto
  hypB _ _ ([18] {jk = ₁₂}) = by-basis-change (X₀₁ • X₁₂) (axiom [S17]) 10 auto
  hypB _ _ ([18] {jk = ₁₃}) = by-basis-change (X₀₁ • X₁₃) (axiom [S17]) 30 auto
  hypB _ _ ([18] {jk = ₂₃}) = by-basis-change (X₀₂ • X₁₃) (axiom [S17]) 20 auto
  hypB _ _ ([19] {jk = ₀₁}) = axiom [S18]
  hypB _ _ ([19] {jk = ₀₂}) = by-basis-change X₁₂ (axiom [S18]) 20 auto
  hypB _ _ ([19] {jk = ₀₃}) = by-basis-change X₁₃ (axiom [S18]) 50 auto
  hypB _ _ ([19] {jk = ₁₂}) = by-basis-change (X₀₁ • X₁₂) (axiom [S18]) 30 auto
  hypB _ _ ([19] {jk = ₁₃}) = by-basis-change (X₀₁ • X₁₃) (axiom [S18]) 50 auto
  hypB _ _ ([19] {jk = ₂₃}) = by-basis-change (X₀₂ • X₁₃) (axiom [S18]) 70 auto
  hypB _ _ ([20] {jk = ₀₁} {₁₂} {₂₃} {₀₂} {₁₃}) = axiom [S19]
  hypB _ _ ([20] {jk = ₀₁} {₁₃} {lt = ()})
  hypB _ _ ([20] {jk = ₀₂} {₂₃} {lt = ()})
  hypB _ _ ([20] {jk = ₀₃} {kl = ()})
  hypB _ _ ([20] {jk = ₁₂} {₂₃} {lt = ()})
  hypB _ _ ([20] {jk = ₁₃} {kl = ()})
  hypB _ _ ([20] {jk = ₂₃} {kl = ()})

-- Completeness of the new relations.
theorem-greylyn-of-simple : (w v : Word Generator) -> G.Rel ⊢ greylyn-of-simple w === greylyn-of-simple v -> Rel ⊢ w === v
theorem-greylyn-of-simple = reidemeister-schreier-simplified greylyn-of-simple-gen simple-of-greylyn-gen Greylyn-Simplified-Proofs.hypA Greylyn-Simplified-Proofs.hypB

-- A special case of completeness for words that are in the image of
-- simple-of-greylyn. This is all we actually need in the proof of
-- the main completeness theorem in Completeness.agda.
theorem-simple-of-greylyn : {w v : Word Greylyn.Generator} -> G.Rel ⊢ w === v -> Rel ⊢ simple-of-greylyn w === simple-of-greylyn v
theorem-simple-of-greylyn = lemma-b greylyn-of-simple-gen simple-of-greylyn-gen Greylyn-Simplified-Proofs.hypA Greylyn-Simplified-Proofs.hypB
