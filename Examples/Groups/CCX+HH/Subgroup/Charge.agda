------------------------------------------------------------------------
-- Presentations of groups
--
-- Charge of embedded words and duplicate spectator blocks.
--
-- The action ignores level names.  Its three generator actions commute
-- and are involutions, so every word acts as an involution.  Consequently
-- two differently embedded copies of the same word have charge 00.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Subgroup.Charge where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; gen ; word)
open import Examples.Groups.CCX+HH.Subgroup.Action
import Examples.Groups.CCX+HH.Subgroup.State as State

private variable m n : ℕ

state : ∀ {n} → Coset → Word (T.Gen n) → Coset
state = State.state dyadic-step

gen-involutive : ∀ {n} c (g : T.Gen n) → dyadic-step (dyadic-step c g) g ≡ c
gen-involutive c00 (T.M-gen _) = Eq.refl
gen-involutive c00 (T.X-gen _ _ _) = Eq.refl
gen-involutive c00 (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-involutive c10 (T.M-gen _) = Eq.refl
gen-involutive c10 (T.X-gen _ _ _) = Eq.refl
gen-involutive c10 (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-involutive c11 (T.M-gen _) = Eq.refl
gen-involutive c11 (T.X-gen _ _ _) = Eq.refl
gen-involutive c11 (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-involutive c01 (T.M-gen _) = Eq.refl
gen-involutive c01 (T.X-gen _ _ _) = Eq.refl
gen-involutive c01 (T.K-gen _ _ _ _ _ _ _) = Eq.refl

gen-commute : ∀ {n} c (g h : T.Gen n) →
  dyadic-step (dyadic-step c g) h ≡ dyadic-step (dyadic-step c h) g
gen-commute c00 (T.M-gen _) (T.M-gen _) = Eq.refl
gen-commute c00 (T.M-gen _) (T.X-gen _ _ _) = Eq.refl
gen-commute c00 (T.M-gen _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c00 (T.X-gen _ _ _) (T.M-gen _) = Eq.refl
gen-commute c00 (T.X-gen _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c00 (T.X-gen _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c00 (T.K-gen _ _ _ _ _ _ _) (T.M-gen _) = Eq.refl
gen-commute c00 (T.K-gen _ _ _ _ _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c00 (T.K-gen _ _ _ _ _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c10 (T.M-gen _) (T.M-gen _) = Eq.refl
gen-commute c10 (T.M-gen _) (T.X-gen _ _ _) = Eq.refl
gen-commute c10 (T.M-gen _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c10 (T.X-gen _ _ _) (T.M-gen _) = Eq.refl
gen-commute c10 (T.X-gen _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c10 (T.X-gen _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c10 (T.K-gen _ _ _ _ _ _ _) (T.M-gen _) = Eq.refl
gen-commute c10 (T.K-gen _ _ _ _ _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c10 (T.K-gen _ _ _ _ _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c11 (T.M-gen _) (T.M-gen _) = Eq.refl
gen-commute c11 (T.M-gen _) (T.X-gen _ _ _) = Eq.refl
gen-commute c11 (T.M-gen _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c11 (T.X-gen _ _ _) (T.M-gen _) = Eq.refl
gen-commute c11 (T.X-gen _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c11 (T.X-gen _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c11 (T.K-gen _ _ _ _ _ _ _) (T.M-gen _) = Eq.refl
gen-commute c11 (T.K-gen _ _ _ _ _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c11 (T.K-gen _ _ _ _ _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c01 (T.M-gen _) (T.M-gen _) = Eq.refl
gen-commute c01 (T.M-gen _) (T.X-gen _ _ _) = Eq.refl
gen-commute c01 (T.M-gen _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c01 (T.X-gen _ _ _) (T.M-gen _) = Eq.refl
gen-commute c01 (T.X-gen _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c01 (T.X-gen _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-commute c01 (T.K-gen _ _ _ _ _ _ _) (T.M-gen _) = Eq.refl
gen-commute c01 (T.K-gen _ _ _ _ _ _ _) (T.X-gen _ _ _) = Eq.refl
gen-commute c01 (T.K-gen _ _ _ _ _ _ _) (T.K-gen _ _ _ _ _ _ _) = Eq.refl

gen-word-commute : ∀ {n} c (g : T.Gen n) w →
  state (dyadic-step c g) w ≡ dyadic-step (state c w) g
gen-word-commute c g [ h ]ʷ = gen-commute c g h
gen-word-commute c g ε = Eq.refl
gen-word-commute c g (u • v) =
  Eq.trans (Eq.cong (λ d → state d v) (gen-word-commute c g u))
           (gen-word-commute (state c u) g v)

word-commute : ∀ {n} c (u v : Word (T.Gen n)) →
  state (state c u) v ≡ state (state c v) u
word-commute c [ g ]ʷ v = gen-word-commute c g v
word-commute c ε v = Eq.refl
word-commute c (u • w) v =
  Eq.trans (word-commute (state c u) w v)
    (Eq.cong (λ d → state d w) (word-commute c u v))

word-involutive : ∀ {n} c (w : Word (T.Gen n)) → state (state c w) w ≡ c
word-involutive c [ g ]ʷ = gen-involutive c g
word-involutive c ε = Eq.refl
word-involutive c (u • v) =
  Eq.trans (Eq.cong (λ d → state d v) (word-commute (state c u) v u))
    (Eq.trans (Eq.cong (λ d → state (state d v) v) (word-involutive c u))
              (word-involutive c v))

gen-embedding : (e : Emb m n) → ∀ c g → dyadic-step c (gen e g) ≡ dyadic-step c g
gen-embedding e c00 (T.M-gen _) = Eq.refl
gen-embedding e c00 (T.X-gen _ _ _) = Eq.refl
gen-embedding e c00 (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-embedding e c10 (T.M-gen _) = Eq.refl
gen-embedding e c10 (T.X-gen _ _ _) = Eq.refl
gen-embedding e c10 (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-embedding e c11 (T.M-gen _) = Eq.refl
gen-embedding e c11 (T.X-gen _ _ _) = Eq.refl
gen-embedding e c11 (T.K-gen _ _ _ _ _ _ _) = Eq.refl
gen-embedding e c01 (T.M-gen _) = Eq.refl
gen-embedding e c01 (T.X-gen _ _ _) = Eq.refl
gen-embedding e c01 (T.K-gen _ _ _ _ _ _ _) = Eq.refl

word-embedding : (e : Emb m n) → ∀ c w → state c (word e w) ≡ state c w
word-embedding e c [ g ]ʷ = gen-embedding e c g
word-embedding e c ε = Eq.refl
word-embedding e c (u • v) =
  Eq.trans (Eq.cong (λ d → state d (word e v)) (word-embedding e c u))
           (word-embedding e (state c u) v)

parallel-closed : (e f : Emb m n) → ∀ c w →
  state c (word e w • word f w) ≡ c
parallel-closed e f c w =
  Eq.trans (Eq.cong (λ d → state d (word f w)) (word-embedding e c w))
    (Eq.trans (word-embedding f (state c w) w) (word-involutive c w))
