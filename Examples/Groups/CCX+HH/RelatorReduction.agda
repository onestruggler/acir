------------------------------------------------------------------------
-- Presentations of groups
--
-- Proof-producing reduction of relators over involutive generators.
-- Adjacent equal letters cancel.  A finite certificate then records a
-- conjugating prefix, a cyclic rotation and optional reversal of a
-- selected relator.  Only syntactic list equality is trusted by the
-- certificate; the group-theoretic reduction is proved below.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Examples.Groups.CCX+HH.RelatorReduction {X : Set} (_≟_ : DecidableEquality X) where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Empty using (⊥)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; reverse)
import Data.List.Properties as LP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_,_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.GroupLike as GL
import Presentation.Tactic.AssociativitySolver as Assoc

private module Flat = Assoc.Assoc (λ (_ _ : Word X) → ⊥)

letters : Word X → List X
letters = Flat.to-list

read : List X → Word X
read = Flat.from-list

push : X → List X → List X
push x [] = x ∷ []
push x (y ∷ ys) with x ≟ y
... | yes _ = ys
... | no _ = x ∷ y ∷ ys

reduce : List X → List X
reduce [] = []
reduce (x ∷ xs) = push x (reduce xs)

rotate : ℕ → List X → List X
rotate zero xs = xs
rotate (suc n) [] = []
rotate (suc n) (x ∷ xs) = rotate n (xs ++ (x ∷ []))

orient : Bool → List X → List X
orient false xs = xs
orient true xs = reverse xs

relator : Word X → Word X → List X
relator u v = letters u ++ reverse (letters v)

record Certificate (raw selected : List X) : Set where
  constructor certificate
  field
    prefix : List X
    turns : ℕ
    backwards : Bool
    checked : reduce raw ≡ prefix ++ (rotate turns (orient backwards selected) ++ reverse prefix)

module Theory (Γ : WRel X)
  (involution : ∀ x → PB._≈_ Γ ([ x ]ʷ • [ x ]ʷ) ε) where

  open PB Γ
  open Assoc.Assoc Γ using (by-assoc ; fl-homo ; lemma-ft)

  private
    gl : GL.Grouplike Γ
    gl x = [ x ]ʷ , involution x
    module G = GL.Group-Lemmas Γ gl

  push-correct : ∀ x xs → [ x ]ʷ • read xs ≈ read (push x xs)
  push-correct x [] = refl
  push-correct x (y ∷ ys) with x ≟ y
  ... | yes Eq.refl = trans (sym assoc) (trans (cong (involution x) refl) left-unit)
  ... | no _ = refl

  reduce-correct : ∀ xs → read xs ≈ read (reduce xs)
  reduce-correct [] = refl
  reduce-correct (x ∷ xs) = trans (cong refl (reduce-correct xs)) (push-correct x (reduce xs))

  reverse-correct : ∀ xs → read (reverse xs) ≈ G._⁻¹ (read xs)
  reverse-correct [] = refl
  reverse-correct (x ∷ xs) = trans (refl' (Eq.cong read (LP.reverse-++ (x ∷ []) xs)))
    (trans (fl-homo (reverse xs) (x ∷ [])) (cong (reverse-correct xs) right-unit))

  inverse-list : ∀ xs → read xs • read (reverse xs) ≈ ε
  inverse-list xs = trans (cong refl (reverse-correct xs)) (G.inverseʳ {g = read xs})

  reverse-trivial : ∀ xs → read xs ≈ ε → read (reverse xs) ≈ ε
  reverse-trivial xs eq = trans (reverse-correct xs) (G.⁻¹-cong eq)

  rotate-once : ∀ x xs → read (x ∷ xs) ≈ ε → read (xs ++ (x ∷ [])) ≈ ε
  rotate-once x xs eq = trans (fl-homo xs (x ∷ []))
    (trans (cong refl right-unit) claim)
    where
    claim : read xs • [ x ]ʷ ≈ ε
    claim = G.•-cancelˡ {g = [ x ]ʷ}
      (trans (sym assoc)
        (trans (cong eq refl) (trans left-unit (sym right-unit))))

  rotate-trivial : ∀ n xs → read xs ≈ ε → read (rotate n xs) ≈ ε
  rotate-trivial zero xs eq = eq
  rotate-trivial (suc n) [] eq = refl
  rotate-trivial (suc n) (x ∷ xs) eq = rotate-trivial n (xs ++ (x ∷ [])) (rotate-once x xs eq)

  orient-trivial : ∀ b xs → read xs ≈ ε → read (orient b xs) ≈ ε
  orient-trivial false xs eq = eq
  orient-trivial true xs eq = reverse-trivial xs eq

  rotate-once-reflect : ∀ x xs → read (xs ++ (x ∷ [])) ≈ ε → read (x ∷ xs) ≈ ε
  rotate-once-reflect x xs eq = G.•-cancelʳ {h = [ x ]ʷ}
    (trans assoc (trans (cong refl product-trivial) (trans right-unit (sym left-unit))))
    where
    product-trivial : read xs • [ x ]ʷ ≈ ε
    product-trivial = trans (cong refl (sym right-unit))
      (trans (sym (fl-homo xs (x ∷ []))) eq)

  rotate-reflect : ∀ n xs → read (rotate n xs) ≈ ε → read xs ≈ ε
  rotate-reflect zero xs eq = eq
  rotate-reflect (suc n) [] eq = refl
  rotate-reflect (suc n) (x ∷ xs) eq =
    rotate-once-reflect x xs (rotate-reflect n (xs ++ (x ∷ [])) eq)

  orient-reflect : ∀ b xs → read (orient b xs) ≈ ε → read xs ≈ ε
  orient-reflect false xs eq = eq
  orient-reflect true xs eq = G.⁻¹-injective
    (trans (sym (reverse-correct xs)) eq)

  conjugate-trivial : ∀ prefix middle → read middle ≈ ε →
    read (prefix ++ (middle ++ reverse prefix)) ≈ ε
  conjugate-trivial prefix middle eq = trans (fl-homo prefix (middle ++ reverse prefix))
    (trans (cong refl (fl-homo middle (reverse prefix)))
      (trans (cong refl (trans (cong eq refl) left-unit)) (inverse-list prefix)))

  conjugate-reflect : ∀ prefix middle →
    read (prefix ++ (middle ++ reverse prefix)) ≈ ε → read middle ≈ ε
  conjugate-reflect prefix middle eq = G.•-cancelʳ {h = read (reverse prefix)}
    (trans (G.•-cancelˡ {g = read prefix}
      (trans (cong refl (sym (fl-homo middle (reverse prefix))))
        (trans (sym (fl-homo prefix (middle ++ reverse prefix)))
          (trans eq (sym (inverse-list prefix)))))) (sym left-unit))

  derive-relator : ∀ {raw selected} → Certificate raw selected → read selected ≈ ε → read raw ≈ ε
  derive-relator {raw} {selected} record { prefix = p ; turns = k ; backwards = b ; checked = check } eq =
    trans (reduce-correct raw)
      (trans (refl' (Eq.cong read check))
        (conjugate-trivial p (rotate k (orient b selected))
          (rotate-trivial k (orient b selected) (orient-trivial b selected eq))))

  recover-selected : ∀ {raw selected} → Certificate raw selected → read raw ≈ ε → read selected ≈ ε
  recover-selected {raw} {selected} record { prefix = p ; turns = k ; backwards = b ; checked = check } eq =
    orient-reflect b selected
      (rotate-reflect k (orient b selected)
        (conjugate-reflect p (rotate k (orient b selected))
          (trans (refl' (Eq.cong read (Eq.sym check))) (trans (sym (reduce-correct raw)) eq))))

  relator-correct : ∀ u v → read (relator u v) ≈ u • G._⁻¹ v
  relator-correct u v = trans (fl-homo (letters u) (reverse (letters v)))
    (cong (lemma-ft {w = u})
      (trans (reverse-correct (letters v)) (G.⁻¹-cong (lemma-ft {w = v}))))

  equation-to-relator : ∀ {u v} → u ≈ v → read (relator u v) ≈ ε
  equation-to-relator {u} {v} eq = trans (relator-correct u v)
    (trans (cong eq refl) (G.inverseʳ {g = v}))

  relator-to-equation : ∀ {u v} → read (relator u v) ≈ ε → u ≈ v
  relator-to-equation {u} {v} eq = G.•-cancelʳ {h = G._⁻¹ v}
    (trans (sym (relator-correct u v)) (trans eq (sym (G.inverseʳ {g = v}))))

  derive-equation : ∀ {u v selected} → Certificate (relator u v) selected →
    read selected ≈ ε → u ≈ v
  derive-equation cert eq = relator-to-equation (derive-relator cert eq)
