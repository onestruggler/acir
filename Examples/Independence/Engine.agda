------------------------------------------------------------------------
-- Presentations of groups
--
-- A proof engine for equations between concrete circuits of a fragment
--
-- After Examples.Groups.Real-Clifford.Engine, for any fragment in a
-- PROP.  An equation is a pair of letter lists with a derivation (Eqn).
-- A derivation of a new equation is a list of steps run on the letters:
-- `perm ys` replaces the current list by ys, which must be the same
-- word up to the commutation of letters on disjoint wires (the
-- canonical forms of Presentation.Tactics.Words.Commuting agree), and
-- `rw i e` rewrites the occurrence of lhs e at position i to rhs e.
-- `run` executes the steps, and run-sound turns a successful run into a
-- derivation, so that a proof is a list of steps closed by refl.
-- Equations are transformed by sym⁼ and lift⁼ (one wire up), and built
-- from equations between words by eqnʷ.  Lists are in the order of
-- words: diagram order, the head first.
--
-- The engine needs a decidable equality on gates and a code for their
-- order, and that the fragment has one scalar (its 0-ary gates are all
-- equal), which makes every scalar central.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool ; true)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Examples.Independence.Engine
  (Gate : ℕ → Set)
  (gate-eq : ∀ {k} → Gate k → Gate k → Bool)
  (gate-eq-sound : ∀ {k} (a b : Gate k) → gate-eq a b ≡ true → a ≡ b)
  (code : ∀ {k} → Gate k → ℕ)
  (one : (h h' : Gate 0) → h ≡ h')
  where

open import Data.Bool.Base using (false ; if_then_else_ ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop ; map)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (zero ; suc ; _<ᵇ_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (commutes ; module Commuting)
open import Presentation.Tactics.Words using (module Associative)

open import Notations using (₁₊)
open import Examples.Independence.Prop Gate

open Associative using (word-of-list ; lemma-append)
open import Presentation.Tactic.AssociativitySolver using (module Assoc)


private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Equality and order of letters

eqP : PGate k → PGate k → Bool
eqP ⌈ a ⌉ ⌈ b ⌉ = gate-eq a b
eqP ⌈ a ⌉ swap  = false
eqP swap  ⌈ b ⌉ = false
eqP swap  swap  = true

eqP-sound : (a b : PGate k) → eqP a b ≡ true → a ≡ b
eqP-sound ⌈ a ⌉ ⌈ b ⌉ h = Eq.cong ⌈_⌉ (gate-eq-sound a b h)
eqP-sound swap  swap  _ = refl
eqP-sound ⌈ a ⌉ swap  ()
eqP-sound swap  ⌈ b ⌉ ()

eqG : Gen n → Gen n → Bool
eqG (gate₀ a) (gate₀ b) = eqP a b
eqG (gate₀ a) (gate₁ b) = false
eqG (gate₀ a) (gate₂ b) = false
eqG (gate₀ a) (y ↥)     = false
eqG (gate₁ a) (gate₀ b) = false
eqG (gate₁ a) (gate₁ b) = eqP a b
eqG (gate₁ a) (gate₂ b) = false
eqG (gate₁ a) (y ↥)     = false
eqG (gate₂ a) (gate₀ b) = false
eqG (gate₂ a) (gate₁ b) = false
eqG (gate₂ a) (gate₂ b) = eqP a b
eqG (gate₂ a) (y ↥)     = false
eqG (x ↥)     (gate₀ b) = false
eqG (x ↥)     (gate₁ b) = false
eqG (x ↥)     (gate₂ b) = false
eqG (x ↥)     (y ↥)     = eqG x y

eqG-sound : (x y : Gen n) → eqG x y ≡ true → x ≡ y
eqG-sound (gate₀ a) (gate₀ b) h = Eq.cong gate₀ (eqP-sound a b h)
eqG-sound (gate₁ a) (gate₁ b) h = Eq.cong gate₁ (eqP-sound a b h)
eqG-sound (gate₂ a) (gate₂ b) h = Eq.cong gate₂ (eqP-sound a b h)
eqG-sound (x ↥)     (y ↥)     h = Eq.cong _↥ (eqG-sound x y h)
eqG-sound (gate₀ a) (gate₁ b) ()
eqG-sound (gate₀ a) (gate₂ b) ()
eqG-sound (gate₀ a) (y ↥)     ()
eqG-sound (gate₁ a) (gate₀ b) ()
eqG-sound (gate₁ a) (gate₂ b) ()
eqG-sound (gate₁ a) (y ↥)     ()
eqG-sound (gate₂ a) (gate₀ b) ()
eqG-sound (gate₂ a) (gate₁ b) ()
eqG-sound (gate₂ a) (y ↥)     ()
eqG-sound (x ↥)     (gate₀ b) ()
eqG-sound (x ↥)     (gate₁ b) ()
eqG-sound (x ↥)     (gate₂ b) ()

eqL : List (Gen n) → List (Gen n) → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqG x y ∧ eqL xs ys

eqL-sound : (xs ys : List (Gen n)) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h with eqG x y in e
eqL-sound (x ∷ xs) (y ∷ ys) h  | true  = Eq.cong₂ _∷_ (eqG-sound x y e) (eqL-sound xs ys h)
eqL-sound (x ∷ xs) (y ∷ ys) () | false

-- The order of the canonical forms: by height, then by arity, then by
-- the code of the gate.
codeP : PGate k → ℕ
codeP ⌈ a ⌉ = suc (code a)
codeP swap  = zero

less : Gen n → Gen n → Bool
less (x ↥)     (y ↥)     = less x y
less (x ↥)     _         = false
less (gate₀ a) (y ↥)     = true
less (gate₁ a) (y ↥)     = true
less (gate₂ a) (y ↥)     = true
less (gate₀ a) (gate₀ b) = codeP a <ᵇ codeP b
less (gate₀ a) _         = true
less (gate₁ a) (gate₀ b) = false
less (gate₁ a) (gate₁ b) = codeP a <ᵇ codeP b
less (gate₁ a) (gate₂ b) = true
less (gate₂ a) (gate₂ b) = codeP a <ᵇ codeP b
less (gate₂ a) _         = false

------------------------------------------------------------------------
-- Letter lists as circuits

⟪_⟫ : List (Gen n) → Circuit n
⟪_⟫ = word-of-list

-- Shifting the letters shifts the word.
⟪map↥⟫ : (xs : List (Gen n)) → ⟪ map _↥ xs ⟫ ≡ ⟪ xs ⟫ ↑
⟪map↥⟫ []       = refl
⟪map↥⟫ (x ∷ xs) = Eq.cong ([ x ↥ ]ʷ •_) (⟪map↥⟫ xs)

------------------------------------------------------------------------
-- The fragment

module Kit
  {Rule : Set} (arity : Rule → ℕ)
  (lhs rhs : (r : Rule) → Circuit (arity r))
  where

  open Fragment arity lhs rhs

  private
    one′ : (h h' : PGate 0) → h ≡ h'
    one′ ⌈ a ⌉ ⌈ b ⌉ = Eq.cong ⌈_⌉ (one a b)

  open Single-Scalar one′ public using (comm₀)

  module _ {n : ℕ} where

    open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong)

    ⟪++⟫ : (xs ys : List (Gen n)) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
    ⟪++⟫ xs ys = sym (lemma-append xs ys)

    ⟪≈⟫ : {xs ys : List (Gen n)} → xs ≡ ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
    ⟪≈⟫ Eq.refl = refl

  ----------------------------------------------------------------------
  -- Commutation

  -- Letters on disjoint wires commute; the scalar commutes with all.
  comm? : (x y : Gen n) → Maybe (commutes (n VRel,_===_) x y)
  comm? x             (gate₀ h)     = just (comm₀ h x)
  comm? (gate₀ h)     y             = just (PB.sym (comm₀ h y))
  comm? (gate₁ h)     (y ↥)         = just (PB.sym (PB.axiom (comm₁ h y)))
  comm? (y ↥)         (gate₁ h)     = just (PB.axiom (comm₁ h y))
  comm? (gate₂ h)     ((y ↥) ↥)     = just (PB.sym (PB.axiom (comm₂ h y)))
  comm? ((y ↥) ↥)     (gate₂ h)     = just (PB.axiom (comm₂ h y))
  comm? (x ↥)         (y ↥)         with comm? x y
  ... | just p  = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) p)
  ... | nothing = nothing
  comm? _             _             = nothing

  module Canon {n : ℕ} = Commuting (Gen n) (n VRel,_===_) comm? less
  open Canon using (comm-canonical ; lemma-comm-canonical)

  ----------------------------------------------------------------------
  -- Equations

  record Eqn (n : ℕ) : Set where
    constructor eqn
    field
      lhs⁼ rhs⁼ : List (Gen n)
      prf       : n ⊢ ⟪ lhs⁼ ⟫ ≈ ⟪ rhs⁼ ⟫

  open Eqn public

  sym⁼ : Eqn n → Eqn n
  sym⁼ (eqn l r p) = eqn r l (PB.sym p)

  -- An equation between words, read as one between letter lists: the
  -- lists are the words' letters, whatever their bracketing (typically
  -- both by refl).
  eqnʷ : {w v : Circuit n} (l r : List (Gen n)) → n ⊢ w ≈ v →
         Assoc.to-list (n VRel,_===_) ⟪ l ⟫ ≡ Assoc.to-list (n VRel,_===_) w →
         Assoc.to-list (n VRel,_===_) v ≡ Assoc.to-list (n VRel,_===_) ⟪ r ⟫ → Eqn n
  eqnʷ {n} l r p e₁ e₂ = eqn l r (PB.trans (by-assoc e₁) (PB.trans p (by-assoc e₂)))
    where open PP (n VRel,_===_) using (by-assoc)

  -- One wire up.  The scalar stays the scalar of the wider circuit
  -- (ω↑=ω), so that lifted equations still match the letters of a word.
  lift-gen : Gen n → Gen (₁₊ n)
  lift-gen (gate₀ h) = gate₀ h
  lift-gen g         = g ↥

  module _ {n : ℕ} where

    open PB ((₁₊ n) VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong)

    ⟪map-lift⟫ : (xs : List (Gen n)) → ⟪ map lift-gen xs ⟫ ≈ ⟪ xs ⟫ ↑
    ⟪map-lift⟫ []             = refl
    ⟪map-lift⟫ (gate₀ h ∷ xs) = cong (sym (PB.axiom (ω↑=ω h))) (⟪map-lift⟫ xs)
    ⟪map-lift⟫ (gate₁ h ∷ xs) = cong refl (⟪map-lift⟫ xs)
    ⟪map-lift⟫ (gate₂ h ∷ xs) = cong refl (⟪map-lift⟫ xs)
    ⟪map-lift⟫ ((g ↥) ∷ xs)   = cong refl (⟪map-lift⟫ xs)

  lift⁼ : Eqn n → Eqn (₁₊ n)
  lift⁼ (eqn l r p) = eqn (map lift-gen l) (map lift-gen r)
    (PB.trans (⟪map-lift⟫ l) (PB.trans (lemma-cong↑ ⟪ l ⟫ ⟪ r ⟫ p) (PB.sym (⟪map-lift⟫ r))))

  ----------------------------------------------------------------------
  -- Running a derivation

  data Step (n : ℕ) : Set where
    perm : List (Gen n) → Step n
    rw   : ℕ → Eqn n → Step n

  rewrite-at : ℕ → Eqn n → List (Gen n) → List (Gen n)
  rewrite-at i e xs = take i xs ++ (rhs⁼ e ++ drop (length (lhs⁼ e)) (drop i xs))

  matches-at : ℕ → Eqn n → List (Gen n) → Bool
  matches-at i e xs = eqL (take (length (lhs⁼ e)) (drop i xs)) (lhs⁼ e)

  run : List (Step n) → List (Gen n) → Maybe (List (Gen n))
  run []              xs = just xs
  run (perm ys ∷ ss)  xs =
    if eqL (comm-canonical xs) (comm-canonical ys) then run ss ys else nothing
  run (rw i e ∷ ss)   xs =
    if matches-at i e xs then run ss (rewrite-at i e xs) else nothing

  module _ {n : ℕ} where

    open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong)

    perm-sound : (xs ys : List (Gen n)) → comm-canonical xs ≡ comm-canonical ys →
                 ⟪ xs ⟫ ≈ ⟪ ys ⟫
    perm-sound xs ys e =
      trans (lemma-comm-canonical xs) (trans (⟪≈⟫ e) (sym (lemma-comm-canonical ys)))

    rw-sound : (i : ℕ) (e : Eqn n) (xs : List (Gen n)) → matches-at i e xs ≡ true →
               ⟪ xs ⟫ ≈ ⟪ rewrite-at i e xs ⟫
    rw-sound i e xs h = begin
      ⟪ xs ⟫                                          ≈⟨ ⟪≈⟫ (Eq.sym (take++drop≡id i xs)) ⟩
      ⟪ take i xs ++ drop i xs ⟫                      ≈⟨ ⟪++⟫ (take i xs) (drop i xs) ⟩
      ⟪ take i xs ⟫ • ⟪ drop i xs ⟫                   ≈⟨ cong refl (⟪≈⟫ (Eq.sym (take++drop≡id m (drop i xs)))) ⟩
      ⟪ take i xs ⟫ • ⟪ take m (drop i xs) ++ rest ⟫  ≈⟨ cong refl (⟪++⟫ (take m (drop i xs)) rest) ⟩
      ⟪ take i xs ⟫ • (⟪ take m (drop i xs) ⟫ • ⟪ rest ⟫)
                                                      ≈⟨ cong refl (cong (⟪≈⟫ (eqL-sound _ _ h)) refl) ⟩
      ⟪ take i xs ⟫ • (⟪ lhs⁼ e ⟫ • ⟪ rest ⟫)         ≈⟨ cong refl (cong (prf e) refl) ⟩
      ⟪ take i xs ⟫ • (⟪ rhs⁼ e ⟫ • ⟪ rest ⟫)         ≈⟨ cong refl (sym (⟪++⟫ (rhs⁼ e) rest)) ⟩
      ⟪ take i xs ⟫ • ⟪ rhs⁼ e ++ rest ⟫              ≈⟨ sym (⟪++⟫ (take i xs) (rhs⁼ e ++ rest)) ⟩
      ⟪ rewrite-at i e xs ⟫                           ∎
      where
      open SR (PP.word-setoid (n VRel,_===_))
      m = length (lhs⁼ e)
      rest = drop m (drop i xs)

    run-sound : (ss : List (Step n)) (xs ys : List (Gen n)) → run ss xs ≡ just ys →
                ⟪ xs ⟫ ≈ ⟪ ys ⟫
    run-sound []             xs ys Eq.refl = refl
    run-sound (perm zs ∷ ss) xs ys h with eqL (comm-canonical xs) (comm-canonical zs) in c
    run-sound (perm zs ∷ ss) xs ys h  | true  =
      trans (perm-sound xs zs (eqL-sound _ _ c)) (run-sound ss zs ys h)
    run-sound (perm zs ∷ ss) xs ys () | false
    run-sound (rw i e ∷ ss)  xs ys h with matches-at i e xs in c
    run-sound (rw i e ∷ ss)  xs ys h  | true  =
      trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
    run-sound (rw i e ∷ ss)  xs ys () | false

  -- A derivation: an equation from the steps that turn lhs into rhs.
  derive : (l r : List (Gen n)) (ss : List (Step n)) → run ss l ≡ just r → Eqn n
  derive l r ss h = eqn l r (run-sound ss l r h)
