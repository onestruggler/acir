------------------------------------------------------------------------
-- Presentations of groups
--
-- Free monoids (words) over a set of generators
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Base where

open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Product using (_×_ ; _,_)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

open import Notations

private
  variable
    A B C X Y H N : Set

------------------------------------------------------------------------
-- Fixity declarations

infix  8 _^_ _^'_
infixr 7 _•_
infixl 9 _ʷ _ᵗ _ᵗ'
infixl 9 _ʰ _ⁿ

------------------------------------------------------------------------
-- Words

-- Words in the language of monoids over a set of generators X.  A
-- word is either a singleton generator, the empty word, or a
-- concatenation of two words.
data Word (X : Set) : Set where
  [_]ʷ : X → Word X
  ε    : Word X
  _•_  : Word X → Word X → Word X

-- Right-associative power: w ^ n = w • (w • … • w) (n times).
_^_ : Word X → ℕ → Word X
w ^ zero  = ε
w ^ ₁₊ zero = w
w ^ ₂₊ n  = w • (w ^ ₁₊ n)

-- Left-associative power: w ^' n = (w • … • w) • w (n times).
_^'_ : Word X → ℕ → Word X
w ^' zero  = ε
w ^' ₁₊ zero = w
w ^' ₂₊ n  = (w ^' ₁₊ n) • w

------------------------------------------------------------------------
-- Functorial operations

-- Functorial map.
wmap : (f : A → B) → Word A → Word B
wmap f [ x ]ʷ   = [ f x ]ʷ
wmap f ε        = ε
wmap f (w • w₁) = wmap f w • wmap f w₁

-- Flatten a word of words.
wconcat : Word (Word A) → Word A
wconcat [ ws ]ʷ    = ws
wconcat ε          = ε
wconcat (ws • ws₁) = wconcat ws • wconcat ws₁

-- Monadic bind: extend f : A → Word B to Word A → Word B.
wconcatmap : (f : A → Word B) → Word A → Word B
wconcatmap f = wconcat ∘ wmap f

-- Postfix notation for wconcatmap: (f ʷ) is the unique monoid
-- homomorphism extending f, written this way throughout the library.
_ʷ : (X → Word Y) → (Word X → Word Y)
_ʷ = wconcatmap

------------------------------------------------------------------------
-- Fold operations

-- Right fold over a word.
wfoldr : (A → B → B) → Word A → B → B
wfoldr _⊕_ [ x ]ʷ   b = x ⊕ b
wfoldr _⊕_ ε        b = b
wfoldr _⊕_ (w • w₁) b = wfoldr _⊕_ w (wfoldr _⊕_ w₁ b)

-- Left fold over a word.
wfoldl : (B → A → B) → B → Word A → B
wfoldl _⊕_ b [ x ]ʷ   = b ⊕ x
wfoldl _⊕_ b ε        = b
wfoldl _⊕_ b (w • w₁) = wfoldl _⊕_ (wfoldl _⊕_ b w) w₁

------------------------------------------------------------------------
-- Stateful traversals (coset enumeration)
--
-- A coset action h : C → Y → Word X × C consumes one letter of Y,
-- returning an output word of X and a successor state.  (h ᵗ) extends
-- it to whole words, threading the state left-to-right and
-- concatenating the outputs; (h ᵗ') is the right-to-left mirror for
-- left coset actions.  These drive the Reidemeister–Schreier method in
-- Normalization.Reidemeister-Schreier and Normalization.CosetNF.

-- Left-to-right stateful traversal.
_ᵗ : (C → Y → Word X × C) → (C → Word Y → Word X × C)
_ᵗ h c [ y ]ʷ = h c y
_ᵗ h c ε      = ε , c
_ᵗ h c (w • u) with (_ᵗ h) c w
_ᵗ h c (w • u) | (w' , c') with (_ᵗ h) c' u
_ᵗ h c (w • u) | (w' , c') | (u' , c'') = w' • u' , c''

-- Right-to-left stateful traversal.
_ᵗ' : (Y → C → C × Word X) → (Word Y → C → C × Word X)
_ᵗ' h [ y ]ʷ c = h y c
_ᵗ' h ε      c = c , ε
_ᵗ' h (w • u) c with (_ᵗ' h) u c
_ᵗ' h (w • u) c | (c' , u') with (_ᵗ' h) w c'
_ᵗ' h (w • u) c | (c' , u') | (c'' , w') = c'' , w' • u'

------------------------------------------------------------------------
-- Conjugation helpers

-- wfoldr specialised to conjugation: apply a word of group elements.
_ʰ : (H → N → N) → Word H → N → N
_ʰ = wfoldr

-- Lift a conjugation action pointwise over a word of normals.
_ⁿ : (H → N → N) → H → Word N → Word N
_ⁿ = wmap ∘_

-- Conjugation with a word-valued action (one group element at a time).
_ⁿ' : (H → N → Word N) → H → Word N → Word N
(conj ⁿ') h [ x ]ʷ    = conj h x
(conj ⁿ') h ε         = ε
(conj ⁿ') h (ns • ns₁) = (conj ⁿ') h ns • (conj ⁿ') h ns₁

-- Conjugation with a word-valued action (a word of group elements).
_ʰ' : (H → N → Word N) → Word H → Word N → Word N
(conj ʰ') [ x ]ʷ     ns = (conj ⁿ') x ns
(conj ʰ') ε          ns = ns
(conj ʰ') (hs • hs₁) ns = (conj ʰ') hs ((conj ʰ') hs₁ ns)

------------------------------------------------------------------------
-- Relations on words

-- A relation on Word X (used to specify presentation axioms).
WRel : Set → Set₁
WRel X = Rel (Word X) 0ℓ
