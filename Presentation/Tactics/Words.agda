------------------------------------------------------------------------
-- Presentations of groups
--
-- Tactics for proving judgements between words (from the Bian–Selinger
-- Agda code, CC BY 2.0): equality up to associativity (general-assoc,
-- special-assoc, up-to-assoc) and up to commutativity (general-comm),
-- inverses, proofs by rewriting (with or without standardisation, on
-- syllables, lifted to sums of alphabets), applying a lemma inside a
-- word (in-context), rewrite steps from relations, and changes of
-- basis.  Computer-generated proofs are written with these tactics.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Presentation.Tactics.Words where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open import Presentation.Tactics.Lists hiding (split ; lemma-split)

-- ----------------------------------------------------------------------
-- * Tactics for associativity

module Associative where

  -- This module provides some tactics for proving equations
  -- between words up to associativity and unit laws.
  --
  -- The tactic general-assoc can be used to automatically prove
  -- equalities of ground words (i.e., words that do not contain
  -- variables).  It can be used, for example, like this:
  --
  -- property : Γ ⊢ (H0 • ((CZ • S0) • ε)) === (H0 • (CZ • ε)) • S0
  -- property = general-assoc auto
  --
  -- The tactic special-assoc can be used to automatically prove
  -- equalities of non-ground words (i.e., those potentially
  -- containing variables). It can be used, for example, like this:
  --
  -- property : ∀ a b c -> Γ ⊢ (a • b) • (H0 • c) === a • (b • H0) • c
  -- property = special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto

  open Monoid-Equational

  -- Convert a list of generators to a word.
  word-of-list : ∀ {X} -> List X -> Word X
  word-of-list [] = ε
  word-of-list (x ∷ xs) = [ x ]ʷ • word-of-list xs

  lemma-⌞-map : ∀ {X Y} {Γ : Context (X ∪ Y)} (xs : List X) -> Γ ⊢ ⌞ word-of-list xs === word-of-list (map ⌜_ xs) 
  lemma-⌞-map [] = refl
  lemma-⌞-map {Γ = Γ} (x ∷ xs) with lemma-⌞-map {Γ = Γ} xs
  ... | ih = cong refl ih

  lemma-⌟-map : ∀ {X Y} {Γ : Context (X ∪ Y)} (xs : List Y) -> Γ ⊢ word-of-list xs ⌟ === word-of-list (map _⌝ xs) 
  lemma-⌟-map [] = refl
  lemma-⌟-map {Γ = Γ} (x ∷ xs) with lemma-⌟-map {Γ = Γ} xs
  ... | ih = cong refl ih

  lemma-map : ∀ {A} {Γ : Context A} -> (f : A -> A) -> (∀ (a : A) -> Γ ⊢ [ a ]ʷ === [ f a ]ʷ) -> ∀ (xs : List A) -> Γ ⊢ word-of-list xs === word-of-list (map f xs)
  lemma-map f pf [] = refl
  lemma-map f pf (x ∷ xs) = cong (pf x) (lemma-map f pf xs)

  word-of-list-no-last-ε : ∀ {X} -> List X -> Word X
  word-of-list-no-last-ε [] = ε
  word-of-list-no-last-ε (x ∷ []) = [ x ]ʷ
  word-of-list-no-last-ε (x ∷ xs) = [ x ]ʷ • word-of-list xs

  -- Convert a word to a list of generators. Note that two words w, v
  -- are equal up to associativity and unit laws if and only if
  -- list-of-word w ≡ list-of-word v.
  list-of-word : ∀ {X : Set} (w : Word X) -> List X
  list-of-word ([ x ]ʷ) = x ∷ []
  list-of-word ε = []
  list-of-word (w • u) = list-of-word w ++ list-of-word u


  -- Convert a word to a list of syllables. 
  list-of-word' : ∀ {X : Set} (w : Word X) -> List (Word X)
  list-of-word' ([ x ]ʷ) = [ x ]ʷ ∷ []
  list-of-word' ε = []
  list-of-word' (w • u) = w ∷ list-of-word' u


  -- Lemma: word-of-list of a homomorphism.
  lemma-append : ∀ {X Γ} -> (xs ys : List X) -> Γ ⊢ word-of-list xs • word-of-list ys === word-of-list (xs ++ ys)
  lemma-append [] ys = left-unit
  lemma-append (x ∷ xs) ys =
      equational ([ x ]ʷ • word-of-list xs) • word-of-list ys
              by assoc
          equals [ x ]ʷ • (word-of-list xs • word-of-list ys)
              by right lemma-append xs ys
          equals [ x ]ʷ • word-of-list (xs ++ ys)

  -- Lemma: word-of-list is the inverse of list-of-word, up to associativity.
  lemma-list-of-word : ∀ {X Γ} (w : Word X) -> Γ ⊢ w === word-of-list (list-of-word w)
  lemma-list-of-word ([ x ]ʷ) = right-unit reversed
  lemma-list-of-word ε = refl
  lemma-list-of-word (w • u) =
     equational w • u
             by left lemma-list-of-word w
         equals word-of-list (list-of-word w) • u
             by right lemma-list-of-word u
         equals word-of-list (list-of-word w) • word-of-list (list-of-word u)
             by lemma-append (list-of-word w) (list-of-word u)
         equals word-of-list (list-of-word w ++ list-of-word u)

  -- Lemma: list-of-word is the inverse of word-of-list.
  lemma-word-of-list : ∀ {X} (w : List X) -> w ≡ list-of-word (word-of-list w)
  lemma-word-of-list [] = Eq.refl
  lemma-word-of-list (x ∷ w) = Eq.cong (λ □ → x ∷ □) (lemma-word-of-list w)


  -- A tactic for arbitrary applications of associativity and unit
  -- laws to ground words. This reduces the problem of proving Γ ⊢ w
  -- === v to the problem of proving list-of-word w ≡ list-of-word v,
  -- which can be done automatically if it is by reflexivity.
  general-assoc : ∀ {X Γ} {w v : Word X} -> list-of-word w ≡ list-of-word v -> Γ ⊢ w === v
  general-assoc {X} {Γ} {w} {v} hyp =
     equational w
             by lemma-list-of-word w
         equals word-of-list (list-of-word w)
             by refl' (Eq.cong word-of-list hyp)
         equals word-of-list (list-of-word v)
             by lemma-list-of-word v reversed
         equals v

  -- Another tactic: Here we need to justify a law only "up to
  -- associativity". For example, if we are given Γ ⊢ (X • Y) • Z
  -- === W, and we need to prove Γ ⊢ X • (Y • Z) === ε • W, we can
  -- apply the up-to-assoc tactic to the assumption to get the
  -- conclusion.
  up-to-assoc : ∀ {X Γ} {w v w' v' : Word X} -> (list-of-word w , list-of-word v) ≡ (list-of-word w' , list-of-word v') -> Γ ⊢ w === v -> Γ ⊢ w' === v'
  up-to-assoc {X} {Γ} {w} {v} {w'} {v'} eqs deriv =
      equational w'
              by general-assoc (Eq.cong proj₁ eqs) reversed
          equals w
              by deriv
          equals v
              by general-assoc (Eq.cong proj₂ eqs)
          equals v'

  -- A convenient symbol to use in patterns such as (□ • □) • □.
  □ : Word ⊤
  □ = [ tt ]ʷ

  -- A version of list-of-word that uses another "pattern" word to
  -- guide the conversion. Any subwords corresponding to occurrences
  -- of □ in the pattern word are not reduced further.
  list-of-word-special : ∀ {X} -> Word X -> Word ⊤ -> List (Word X)
  list-of-word-special w ([ tt ]ʷ) = w ∷ []
  list-of-word-special ([ x ]ʷ) ε = [ x ]ʷ ∷ []
  list-of-word-special ([ x ]ʷ) (p • q) = [ x ]ʷ ∷ []
  list-of-word-special ε ε = []
  list-of-word-special ε (p • q) = []
  list-of-word-special (w • v) ε = list-of-word-special w ε ++ list-of-word-special v ε
  list-of-word-special (w • v) (p • q) = list-of-word-special w p ++ list-of-word-special v q

  -- Definition: Flatten a word of words into a word.
  flatten-word : ∀ {X} -> Word (Word X) -> Word X
  flatten-word ([ w ]ʷ) = w
  flatten-word ε = ε
  flatten-word (w • v) = flatten-word w • flatten-word v

  -- Lemma: If two words are equivalent, then so are their flattenings.
  lemma-flatten-word : ∀ {X Γ} -> {xs ys : Word (Word X)} -> ∅ ⊢ xs === ys -> Γ ⊢ flatten-word xs === flatten-word ys 
  lemma-flatten-word (axiom ())
  lemma-flatten-word refl = refl
  lemma-flatten-word (symm hyp) = symm (lemma-flatten-word hyp)
  lemma-flatten-word (trans hyp hyp₁) = trans (lemma-flatten-word hyp) (lemma-flatten-word hyp₁)
  lemma-flatten-word (cong hyp hyp₁) = cong (lemma-flatten-word hyp) (lemma-flatten-word hyp₁)
  lemma-flatten-word assoc = assoc
  lemma-flatten-word left-unit = left-unit
  lemma-flatten-word right-unit = right-unit


 -- Lemma: word-of-list of a homomorphism.
  lemma-append-syl : ∀ {X Γ} -> (xs ys : List (Word X)) -> Γ ⊢ flatten-word (word-of-list xs) • flatten-word (word-of-list ys) === flatten-word (word-of-list (xs ++ ys))
  lemma-append-syl [] ys = left-unit
  lemma-append-syl (x ∷ xs) ys =
      equational (x • flatten-word (word-of-list xs)) • flatten-word (word-of-list ys)
              by assoc
          equals x • (flatten-word (word-of-list xs) • flatten-word (word-of-list ys))
              by right lemma-append-syl xs ys
          equals x • flatten-word (word-of-list (xs ++ ys))

  

  -- Lemma: word-of-list is the inverse of list-of-word-special, up to
  -- flattening.
  lemma-list-of-word-special : ∀ {X Γ} (w : Word X) (p : Word ⊤) -> Γ ⊢ flatten-word (word-of-list (list-of-word-special w p)) === w
  lemma-list-of-word-special w ([ tt ]ʷ) = right-unit
  lemma-list-of-word-special ([ x ]ʷ) ε = right-unit
  lemma-list-of-word-special ([ x ]ʷ) (p • q) = right-unit
  lemma-list-of-word-special ε ε = refl
  lemma-list-of-word-special ε (p • q) = refl
  lemma-list-of-word-special (w • v) ε =
      equational flatten-word (word-of-list (list-of-word-special w ε ++ list-of-word-special v ε))
              by lemma-flatten-word (lemma-append (list-of-word-special w ε) (list-of-word-special v ε)) reversed
          equals flatten-word (word-of-list (list-of-word-special w ε) • word-of-list (list-of-word-special v ε))
              by refl
          equals flatten-word (word-of-list (list-of-word-special w ε)) • flatten-word (word-of-list (list-of-word-special v ε))
              by cong (lemma-list-of-word-special w ε) (lemma-list-of-word-special v ε)
          equals w • v

  lemma-list-of-word-special (w • v) (p • q) = 
      equational flatten-word (word-of-list (list-of-word-special w p ++ list-of-word-special v q))
              by lemma-flatten-word (lemma-append (list-of-word-special w p) (list-of-word-special v q)) reversed
          equals flatten-word (word-of-list (list-of-word-special w p) • word-of-list (list-of-word-special v q))
              by refl
          equals flatten-word (word-of-list (list-of-word-special w p)) • flatten-word (word-of-list (list-of-word-special v q))
              by cong (lemma-list-of-word-special w p) (lemma-list-of-word-special v q)
          equals w • v

  -- A "guided" version of general associativity. Unlike
  -- general-assoc, this also works for non-ground words, i.e., words
  -- that contain variables. This is achieved by giving a pair of
  -- "pattern" words containing □ in all places that should not be
  -- reduced.
  --
  -- For example, to prove Γ ⊢ (a • b) • (c • d) === a • (b • c) • d,
  -- use
  -- special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto.
  --
  -- This even works when a, b, c, d are variables. For added
  -- convenience, ε can be used as a pattern for any determinate
  -- sub-word (i.e., a subword that contains no variables).
  special-assoc : ∀ {X Γ} {w v : Word X} (p q : Word ⊤) -> list-of-word-special w p ≡ list-of-word-special v q -> Γ ⊢ w === v
  special-assoc {w = w} {v = v} p q hyp =
      equational w
              by lemma-list-of-word-special w p reversed
          equals flatten-word (word-of-list (list-of-word-special w p))
              by refl' (Eq.cong (λ □ → flatten-word (word-of-list □)) hyp)
          equals flatten-word (word-of-list (list-of-word-special v q))
              by lemma-list-of-word-special v q
          equals v

-- ----------------------------------------------------------------------
-- * Tactics for commutativity

-- Definition: two generators commute under Γ.
commutes : ∀ {X} -> Context X -> X -> X -> Set
commutes Γ x y = Γ ⊢ [ x ]ʷ • [ y ]ʷ === [ y ]ʷ • [ x ]ʷ

-- Definition: two words commute under Γ.
commutes-word : ∀ {X} -> Context X -> (u v : Word X) -> Set
commutes-word Γ u v = Γ ⊢ u • v === v • u

module Commuting
       (X : Set)
       (Γ : Context X)
       (comm : (x y : X) -> Maybe (commutes Γ x y))
       (less : X -> X -> Bool)
  where

  -- This module provides some tactics for proving equations between
  -- words up to commutativity. We assume given a set X of generators,
  -- a set Γ of relations, and a semi-decidable commutativity relation
  -- (i.e., given generators x and y, comm x y either returns a proof
  -- that x and y commute, or nothing). We also assume a total
  -- ordering 'less' on generators, which is used to find canonical
  -- representatives of words up to commutativity.
  --
  -- The tactic general-comm can be used to automatically prove
  -- equalities of ground words up to commutativity It can be used,
  -- for example, as follows. Here, we assume that Z commutes with X
  -- and Y, but X does not commute with Y:
  --
  -- property : Γ ⊢ X • Y • Z === Z • X • Y
  -- property = general-comm auto
  --
  -- Note that this tactic also includes associativity.

  open Monoid-Equational
  open Associative

  open Presentation.Tactics.Lists.All

  -- ----------------------------------------------------------------------
  -- ** Canonical forms

  -- The primary engine of the commutativity tactic is the function
  -- comm-canonical, which computes the canonical form of a word
  -- modulo commutativity. The canonical form is defined to be the
  -- "smallest" word that is equivalent to the given one. Here,
  -- "smallest" is taken with respect to the reverse (or Hebrew)
  -- lexicographic order.
  --
  -- For example, consider generators A, B, C, D such that A commutes
  -- with C and D; B commutes with D; and no other pair of generators
  -- commutes. Assume A < B < C < D. Then the canonical form of
  -- B,A,D,C,A,B is D,B,C,A,A,B.
  --
  -- The reason we use the reverse lexicographic order is that it
  -- permits a convenient and efficient recursive algorithm for
  -- computing canonical forms. Namely, we can compute the canonical
  -- form of a non-empty list of generators x∷xs by first computing
  -- the canonical form of xs, then inserting x in the correct
  -- position.

  -- Auxiliary function: Given ys, x, and zs, return
  -- (reverse zs1 @ ys , zs2), where zs = zs1 @ zs2 and zs1 is the
  -- longest prefix of zs all of whose elements commute with x.
  split : List X -> X -> List X -> List X × List X
  split ys x [] = (ys , [])
  split ys x (z ∷ zs) with comm x z
  split ys x (z ∷ zs) | nothing = (ys , z ∷ zs)
  split ys x (z ∷ zs) | just _ = split (z ∷ ys) x zs

  -- Auxiliary function: Given ys, x, and zs, return reverse ys' @ zs,
  -- where ys' is the lexicographically smallest word that can be
  -- obtained by inserting x in ys. We assume that reverse ys @ zs is
  -- a canonical form.
  unsplit : List X -> X -> List X -> List X
  unsplit [] x zs = x ∷ zs
  unsplit (y ∷ ys) x zs with less x y
  unsplit (y ∷ ys) x zs | true = unsplit ys x (y ∷ zs)
  unsplit (y ∷ ys) x zs | false = reverse-append (y ∷ ys) (x ∷ zs)

  -- Given x and xs, where xs is already a canonical form, return the
  -- canonical form of x ∷ xs.
  insert : X -> List X -> List X
  insert x xs with split [] x xs
  insert x xs | (ys , zs) = unsplit ys x zs

  -- Return the canonical form of a word, modulo commutativity of
  -- generators.  Of all equivalent words, the canonical form is the
  -- least one in the reverse lexicographic order.
  comm-canonical : List X -> List X
  comm-canonical [] = []
  comm-canonical (x ∷ xs) = insert x (comm-canonical xs)

  -- ----------------------------------------------------------------------
  -- ** Properties of canonical forms.

  -- We prove various technical properties of the functions split,
  -- reverse-append, unsplit, and insert. These will be needed for
  -- proving that every word is equivalent to its canonical form.

  lemma-split1 : (ys : List X) -> (x : X) -> (zs : List X) -> ∀ {ys' zs'} -> split ys x zs ≡ (ys' , zs') -> Γ ⊢ word-of-list (reverse-append ys zs) === word-of-list (reverse-append ys' zs')
  lemma-split1 ys x [] Eq.refl = refl
  lemma-split1 ys x (z ∷ zs) eq with comm x z
  lemma-split1 ys x (z ∷ zs) Eq.refl | nothing = refl
  lemma-split1 ys x (z ∷ zs) eq | just wit = lemma-split1 (z ∷ ys) x zs eq

  lemma-split2 : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] commutes Γ x y -> ∀ {ys' zs'} -> split ys x zs ≡ (ys' , zs') -> All[ y ∈ ys' ] commutes Γ x y
  lemma-split2 ys x [] ih Eq.refl = ih -- ih
  lemma-split2 ys x (z ∷ zs) ih eq with comm x z
  lemma-split2 ys x (z ∷ zs) ih Eq.refl | nothing = ih -- ih
  lemma-split2 ys x (z ∷ zs) ih eq | just wit = lemma-split2 (z ∷ ys) x zs (wit ∷ ih) eq

  lemma-reverse-append-cong : (ys : List X) -> (zs zs' : List X) -> Γ ⊢ word-of-list zs === word-of-list zs' -> Γ ⊢ word-of-list (reverse-append ys zs) === word-of-list (reverse-append ys zs')
  lemma-reverse-append-cong [] zs zs' hyp = hyp
  lemma-reverse-append-cong (y ∷ ys) zs zs' hyp = lemma-reverse-append-cong ys (y ∷ zs) (y ∷ zs') (right hyp)

  lemma-reverse-append : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] commutes Γ x y -> Γ ⊢ word-of-list (x ∷ reverse-append ys zs) === word-of-list (reverse-append ys (x ∷ zs))
  lemma-reverse-append [] x zs [] = refl
  lemma-reverse-append (y ∷ ys) x zs (h ∷ hyp) =
    let ih : Γ ⊢ word-of-list (x ∷ reverse-append ys (y ∷ zs)) === word-of-list (reverse-append ys (x ∷ y ∷ zs))
        ih = lemma-reverse-append ys x (y ∷ zs) hyp

        claim : Γ ⊢ [ x ]ʷ • [ y ]ʷ • word-of-list zs === [ y ]ʷ • [ x ]ʷ • word-of-list zs
        claim = equational [ x ]ʷ • [ y ]ʷ • word-of-list zs
                        by assoc reversed
                    equals ([ x ]ʷ • [ y ]ʷ) • word-of-list zs
                        by left h
                    equals ([ y ]ʷ • [ x ]ʷ) • word-of-list zs
                        by assoc
                    equals [ y ]ʷ • [ x ]ʷ • word-of-list zs
    in
    equational word-of-list (x ∷ reverse-append ys (y ∷ zs))
            by ih
        equals word-of-list (reverse-append ys (x ∷ y ∷ zs))
            by lemma-reverse-append-cong ys (x ∷ y ∷ zs) (y ∷ x ∷ zs) claim
        equals word-of-list (reverse-append ys (y ∷ x ∷ zs))
       
  lemma-unsplit : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] commutes Γ x y -> Γ ⊢ word-of-list (x ∷ reverse-append ys zs) === word-of-list (unsplit ys x zs)
  lemma-unsplit [] x zs hyp = refl
  lemma-unsplit (y ∷ ys) x zs (h ∷ hyp) with less x y
  lemma-unsplit (y ∷ ys) x zs (h ∷ hyp) | true = lemma-unsplit ys x (y ∷ zs) hyp
  lemma-unsplit (y ∷ ys) x zs (h ∷ hyp) | false = lemma-reverse-append (y ∷ ys) x zs (h ∷ hyp)

  lemma-insert : (x : X) -> (xs : List X) -> Γ ⊢ word-of-list (x ∷ xs) === word-of-list (insert x xs)
  lemma-insert x xs with split [] x xs in eq
  ... | (ys , zs) =
      equational word-of-list (x ∷ xs)
              by right lemma-split1 [] x xs eq
          equals word-of-list (x ∷ reverse-append ys zs)
              by lemma-unsplit ys x zs (lemma-split2 [] x xs [] eq)
          equals word-of-list (unsplit ys x zs)

  -- Soundness of comm-canonical: every word is equivalent to its
  -- canonical form.
  lemma-comm-canonical : (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (comm-canonical xs)
  lemma-comm-canonical [] = refl
  lemma-comm-canonical (x ∷ xs) =
    equational word-of-list (x ∷ xs)
            by right (lemma-comm-canonical xs)
        equals word-of-list (x ∷ comm-canonical xs)
            by lemma-insert x (comm-canonical xs)
        equals word-of-list (insert x (comm-canonical xs))

  -- ----------------------------------------------------------------------
  -- ** The general-comm tactic

  -- A tactic for showing that two ground words are equivalent up to
  -- commutativity (and associativity). This works by converting both
  -- words to canonical form and checking that they are equal.
  general-comm : ∀ {w v : Word X} -> comm-canonical (list-of-word w) ≡ comm-canonical (list-of-word v) -> Γ ⊢ w === v
  general-comm {w} {v} hyp =
   equational w
           by lemma-list-of-word w
       equals word-of-list (list-of-word w)
           by lemma-comm-canonical (list-of-word w)
       equals word-of-list (comm-canonical (list-of-word w))
           by refl' (Eq.cong word-of-list hyp)
       equals word-of-list (comm-canonical (list-of-word v))
           by lemma-comm-canonical (list-of-word v) reversed
       equals word-of-list (list-of-word v)
           by lemma-list-of-word v reversed
       equals v

-- ----------------------------------------------------------------------
-- * Tactics for wcommutativity

-- This is like commutativity, but for words of words.

-- Definition: two generators wcommute under Γ.
wcommutes : ∀ {X} -> Context X -> Word X -> Word X -> Set
wcommutes Γ x y = Γ ⊢ x • y === y • x

-- Definition: two words wcommute under Γ.
wcommutes-word : ∀ {X} -> Context X -> (u v : Word (Word X)) -> Set
wcommutes-word Γ u v = Γ ⊢ flatten-word u • flatten-word v === flatten-word v • flatten-word u
  where
    open Associative


module WCommuting
       (X' : Set)
       (Γ : Context X')
       (wcomm : (x y : Word X') -> Maybe (wcommutes Γ x y))
       (less : Word X' -> Word X' -> Bool)
  where

  X = Word X'
  -- This module provides some tactics for proving equations between
  -- words up to wcommutativity. We assume given a set X of generators,
  -- a set Γ of relations, and a semi-decidable wcommutativity relation
  -- (i.e., given generators x and y, wcomm x y either returns a proof
  -- that x and y wcommute, or nothing). We also assume a total
  -- ordering 'less' on generators, which is used to find canonical
  -- representatives of words up to wcommutativity.
  --
  -- The tactic general-wcomm can be used to automatically prove
  -- equalities of ground words up to wcommutativity. It can be used,
  -- for example, as follows. Here, we assume that Z wcommutes with X
  -- and Y, but X does not wcommute with Y:
  --
  -- property : Γ ⊢ X • Y • Z === Z • X • Y
  -- property = general-wcomm auto
  --
  -- Note that this tactic also includes associativity.

  open Monoid-Equational
  open Associative

  open Presentation.Tactics.Lists.All

  -- ----------------------------------------------------------------------
  -- ** Canonical forms

  -- The primary engine of the wcommutativity tactic is the function
  -- wcomm-canonical, which computes the canonical form of a word
  -- modulo wcommutativity. The canonical form is defined to be the
  -- "smallest" word that is equivalent to the given one. Here,
  -- "smallest" is taken with respect to the reverse (or Hebrew)
  -- lexicographic order.
  --
  -- For example, consider generators A, B, C, D such that A wcommutes
  -- with C and D; B wcommutes with D; and no other pair of generators
  -- wcommutes. Assume A < B < C < D. Then the canonical form of
  -- B,A,D,C,A,B is D,B,C,A,A,B.
  --
  -- The reason we use the reverse lexicographic order is that it
  -- permits a convenient and efficient recursive algorithm for
  -- computing canonical forms. Namely, we can compute the canonical
  -- form of a non-empty list of generators x∷xs by first computing
  -- the canonical form of xs, then inserting x in the correct
  -- position.

  -- Auxiliary function: Given ys, x, and zs, return
  -- (reverse zs1 @ ys , zs2), where zs = zs1 @ zs2 and zs1 is the
  -- longest prefix of zs all of whose elements wcommute with x.
  split : List X -> X -> List X -> List X × List X
  split ys x [] = (ys , [])
  split ys x (z ∷ zs) with wcomm x z
  split ys x (z ∷ zs) | nothing = (ys , z ∷ zs)
  split ys x (z ∷ zs) | just _ = split (z ∷ ys) x zs

  -- Auxiliary function: Given ys, x, and zs, return reverse ys' @ zs,
  -- where ys' is the lexicographically smallest word that can be
  -- obtained by inserting x in ys. We assume that reverse ys @ zs is
  -- a canonical form.
  unsplit : List X -> X -> List X -> List X
  unsplit [] x zs = x ∷ zs
  unsplit (y ∷ ys) x zs with less x y
  unsplit (y ∷ ys) x zs | true = unsplit ys x (y ∷ zs)
  unsplit (y ∷ ys) x zs | false = reverse-append (y ∷ ys) (x ∷ zs)

  -- Given x and xs, where xs is already a canonical form, return the
  -- canonical form of x ∷ xs.
  insert : X -> List X -> List X
  insert x xs with split [] x xs
  insert x xs | (ys , zs) = unsplit ys x zs

  -- Return the canonical form of a word, modulo wcommutativity of
  -- generators.  Of all equivalent words, the canonical form is the
  -- least one in the reverse lexicographic order.
  wcomm-canonical : List X -> List X
  wcomm-canonical [] = []
  wcomm-canonical (x ∷ xs) = insert x (wcomm-canonical xs)

  -- ----------------------------------------------------------------------
  -- ** Properties of canonical forms.

  -- We prove various technical properties of the functions split,
  -- reverse-append, unsplit, and insert. These will be needed for
  -- proving that every word is equivalent to its canonical form.

  lemma-split1 : (ys : List X) -> (x : X) -> (zs : List X) -> ∀ {ys' zs'} -> split ys x zs ≡ (ys' , zs') -> Γ ⊢ flatten-word (word-of-list (reverse-append ys zs)) === flatten-word (word-of-list (reverse-append ys' zs'))
  lemma-split1 ys x [] Eq.refl = refl
  lemma-split1 ys x (z ∷ zs) eq with wcomm x z
  lemma-split1 ys x (z ∷ zs) Eq.refl | nothing = refl
  lemma-split1 ys x (z ∷ zs) eq | just wit = lemma-split1 (z ∷ ys) x zs eq

  lemma-split2 : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] wcommutes Γ x y -> ∀ {ys' zs'} -> split ys x zs ≡ (ys' , zs') -> All[ y ∈ ys' ] wcommutes Γ x y
  lemma-split2 ys x [] ih Eq.refl = ih -- ih
  lemma-split2 ys x (z ∷ zs) ih eq with wcomm x z
  lemma-split2 ys x (z ∷ zs) ih Eq.refl | nothing = ih -- ih
  lemma-split2 ys x (z ∷ zs) ih eq | just wit = lemma-split2 (z ∷ ys) x zs (wit ∷ ih) eq

  flatten-word-of-list : List X -> X
  flatten-word-of-list x = flatten-word (word-of-list x)

  lemma-reverse-append-cong : (ys : List X) -> (zs zs' : List X) -> Γ ⊢ flatten-word (word-of-list zs) === flatten-word (word-of-list zs') -> Γ ⊢ flatten-word-of-list (reverse-append ys zs) === flatten-word-of-list (reverse-append ys zs')
  lemma-reverse-append-cong [] zs zs' hyp = hyp
  lemma-reverse-append-cong (y ∷ ys) zs zs' hyp = lemma-reverse-append-cong ys (y ∷ zs) (y ∷ zs') (right hyp)

  lemma-reverse-append : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] wcommutes Γ x y -> Γ ⊢ flatten-word-of-list (x ∷ reverse-append ys zs) === flatten-word-of-list (reverse-append ys (x ∷ zs))
  lemma-reverse-append [] x zs [] = refl
  lemma-reverse-append (y ∷ ys) x zs (h ∷ hyp) =
    let ih : Γ ⊢ flatten-word-of-list (x ∷ reverse-append ys (y ∷ zs)) === flatten-word-of-list (reverse-append ys (x ∷ y ∷ zs))
        ih = lemma-reverse-append ys x (y ∷ zs) hyp

        claim : Γ ⊢ x • y • flatten-word-of-list zs === y • x • flatten-word-of-list zs
        claim = equational x • y • flatten-word-of-list zs
                        by assoc reversed
                    equals (x • y) • flatten-word-of-list zs
                        by left h
                    equals (y • x) • flatten-word-of-list zs
                        by assoc
                    equals y • x • flatten-word-of-list zs
    in
    equational flatten-word-of-list (x ∷ reverse-append ys (y ∷ zs))
            by ih
        equals flatten-word-of-list (reverse-append ys (x ∷ y ∷ zs))
            by lemma-reverse-append-cong ys (x ∷ y ∷ zs) (y ∷ x ∷ zs) claim
        equals flatten-word-of-list (reverse-append ys (y ∷ x ∷ zs))
       
  lemma-unsplit : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] wcommutes Γ x y -> Γ ⊢ flatten-word-of-list (x ∷ reverse-append ys zs) === flatten-word-of-list (unsplit ys x zs)
  lemma-unsplit [] x zs hyp = refl
  lemma-unsplit (y ∷ ys) x zs (h ∷ hyp) with less x y
  lemma-unsplit (y ∷ ys) x zs (h ∷ hyp) | true = lemma-unsplit ys x (y ∷ zs) hyp
  lemma-unsplit (y ∷ ys) x zs (h ∷ hyp) | false = lemma-reverse-append (y ∷ ys) x zs (h ∷ hyp)

  lemma-insert : (x : X) -> (xs : List X) -> Γ ⊢ flatten-word-of-list (x ∷ xs) === flatten-word-of-list (insert x xs)
  lemma-insert x xs with split [] x xs in eq
  ... | (ys , zs) =
      equational flatten-word-of-list (x ∷ xs)
              by right lemma-split1 [] x xs eq
          equals flatten-word-of-list (x ∷ reverse-append ys zs)
              by lemma-unsplit ys x zs (lemma-split2 [] x xs [] eq)
          equals flatten-word-of-list (unsplit ys x zs)

  -- Soundness of wcomm-canonical: every word is equivalent to its
  -- canonical form.
  lemma-wcomm-canonical : (xs : List X) -> Γ ⊢ flatten-word-of-list xs === flatten-word-of-list (wcomm-canonical xs)
  lemma-wcomm-canonical [] = refl
  lemma-wcomm-canonical (x ∷ xs) =
    equational flatten-word-of-list (x ∷ xs)
            by right (lemma-wcomm-canonical xs)
        equals flatten-word-of-list (x ∷ wcomm-canonical xs)
            by lemma-insert x (wcomm-canonical xs)
        equals flatten-word-of-list (insert x (wcomm-canonical xs))


  -- ----------------------------------------------------------------------
  -- ** The general-wcomm tactic

  -- A tactic for showing that two ground words are equivalent up to
  -- wcommutativity (and associativity). This works by converting both
  -- words to canonical form and checking that they are equal.
  general-wcomm : ∀ {w v : Word X'} (pw pv : Word ⊤) -> wcomm-canonical (list-of-word-special w pw) ≡ wcomm-canonical (list-of-word-special v pv) -> Γ ⊢  w === v
  general-wcomm {w} {v} pw pv hyp = -- let w = flatten-word w' in let v = flatten-word v' in
   equational w
           by (lemma-list-of-word-special w pw) reversed
       equals flatten-word-of-list (list-of-word-special w pw)
           by lemma-wcomm-canonical (list-of-word-special w pw)
       equals flatten-word-of-list (wcomm-canonical (list-of-word-special w pw))
           by refl' (Eq.cong flatten-word-of-list hyp)
       equals flatten-word-of-list (wcomm-canonical (list-of-word-special v pv))
           by (lemma-wcomm-canonical (list-of-word-special v pv) reversed)
       equals flatten-word-of-list (list-of-word-special v pv)
           by lemma-list-of-word-special v pv
       equals v

-- ----------------------------------------------------------------------
-- * Some tactics for inverses.

module Inverse
       (X : Set)
       (Γ : Context X)
       (group-like : Grouplike Γ)
  where

  -- This module provides a tactic inverse-eq, which can be used to
  -- prove that two words are equal by proving that their inverses are
  -- equal. It is similar to lemma-rule-inverse (from Word-Lemmas),
  -- except that the final ε on the inverses is omitted.

  open Monoid-Equational
  open Associative
  open Group-Lemmas X Γ group-like public

  -- An alternative version of word-of-list that omits the final ε.
  -- Sometimes this is preferable for cosmetic reasons.
  word-of-list-alt : ∀ {X} -> List X -> Word X
  word-of-list-alt [] = ε
  word-of-list-alt (x ∷ []) = [ x ]ʷ
  word-of-list-alt (x ∷ y ∷ xs) = [ x ]ʷ • word-of-list-alt (y ∷ xs)

  -- Lemma: word-of-list-alt is equivalent to word-of-list.
  lemma-word-of-list-alt : ∀ {X Γ} -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list-alt xs
  lemma-word-of-list-alt [] = refl
  lemma-word-of-list-alt (x ∷ []) = right-unit
  lemma-word-of-list-alt (x ∷ y ∷ xs) = right lemma-word-of-list-alt (y ∷ xs)

  -- A version of lemma-rule-inverse that flattens the inverse, for
  -- convenience.
  inverse-eq : {u v : Word X} -> Γ ⊢ word-of-list-alt (list-of-word (u ⁻¹)) === word-of-list-alt (list-of-word (v ⁻¹)) -> Γ ⊢ u === v
  inverse-eq {u} {v} hyp = lemma-rule-inverse claim
    where
      claim : Γ ⊢ u ⁻¹ === v ⁻¹
      claim =
        equational u ⁻¹
                by lemma-list-of-word (u ⁻¹)
            equals word-of-list (list-of-word (u ⁻¹))
                by lemma-word-of-list-alt (list-of-word (u ⁻¹))
            equals word-of-list-alt (list-of-word (u ⁻¹))
                by hyp
            equals word-of-list-alt (list-of-word (v ⁻¹))
                by lemma-word-of-list-alt (list-of-word (v ⁻¹)) reversed
            equals word-of-list (list-of-word (v ⁻¹))
                by lemma-list-of-word (v ⁻¹) reversed
            equals v ⁻¹


-- ----------------------------------------------------------------------
-- * Some tactics for applying axioms inside words

module InContext where

  -- This module provides some convenient tactics for applying axiom x
  -- at position n in some word. For the purpose of the following
  -- summary, assume there is an axiom
  --
  -- axiom : Γ ⊢ A • B === C • D • E.
  --
  -- The tactic at-head can be used to apply an axiom at the beginning
  -- of a list-like word. A word is list-like if it is of the form A •
  -- (B • (C • ε)), where A, B, C are generators. For example, this
  -- tactic can be used as follows:
  --
  -- property1 : Γ ⊢ A • B • X • Y • ε === C • D • E • X • Y • ε.
  -- property1 = at-head axiom
  --
  -- The tactic "in-context" can be used much more generally to apply
  -- an axiom in some specified position in a word. For example,
  --
  -- property2 : Γ ⊢ X • Y • Z • A • B • W === X • Y • Z • C • D • E • W
  -- property2 = in-context 3 2 auto axiom
  --
  -- Unlike at-head, the components X, Y, Z, A, B, etc., do not need to
  -- be generators; they can be words. The first two arguments of
  -- in-context specify the number of components of the left-hand side
  -- to be skipped (here, X, Y, Z), and the number of components of
  -- the left-hand-side to apply the axiom to (here, A, B).
  --
  -- The tactic in-context is used extensively in computer-generated
  -- proofs, such as the ones found in Equation1.agda, ...,
  -- Equation46.agda.
  --
  -- We also provide a tactic "rewrite-in-context" that is similar to
  -- in-context, but it applies rewriting to the selected subword,
  -- rather than an axiom. Specifically, given a multistep rewrite
  -- function 'multistep' and its associated lemma 'lemma-multistep',
  -- the tactic is used like this:
  --
  -- property3 : Γ ⊢ X • Y • Z • A • B • W === X • Y • Z • C • D • E • W
  -- property3 = rewrite-in-context multistep lemma-multistep 3 2 100 auto
  --
  -- Here, the arguments 3 and 2 are as above, i.e., the pick out the
  -- subword at position 3 and length 2 from the left-hand side (in
  -- this case, A • B). The argument 100 specifies a bound on the
  -- number of rewrite steps to perform. The tactic will then attempt
  -- to rewrite the words A • B and C • D • E to a common normal form.
  -- The tactic fails if this is not possible in the given number of
  -- steps, or if the rest of the words do not agree.


  open Monoid-Equational
  open Associative

  -- Translate the word u₁ • u₂ • ... • uₙ to the list [u₁, u₂, ..., uₙ].
  -- This differs from 'list-of-word' in that u₁, ..., uₙ are words, 
  -- not generators, i.e., we do not flatten subwords.
  list-of-word2 : ∀ {X} -> Word X -> List (Word X)
  list-of-word2 ([ x ]ʷ) = [ x ]ʷ ∷ []
  list-of-word2 ε = ε ∷ []
  list-of-word2 (u • w) = u ∷ list-of-word2 w
    
  -- Translate the list [u₁, u₂, ..., uₙ] to the word u₁ • u₂ • ... • uₙ.
  word-of-list2 : ∀ {X} -> List (Word X) -> Word X
  word-of-list2 [] = ε
  word-of-list2 (u ∷ []) = u
  word-of-list2 (u ∷ v ∷ us) = u • word-of-list2 (v ∷ us)
  
  -- Lemma: word-of-list2 is an inverse of list-of-word2.
  lemma-list-of-word2 : ∀ {X} -> (u : Word X) -> word-of-list2 (list-of-word2 u) ≡ u
  lemma-list-of-word2 ([ x ]ʷ) = Eq.refl
  lemma-list-of-word2 ε = Eq.refl
  lemma-list-of-word2 (u • [ x ]ʷ) = Eq.refl
  lemma-list-of-word2 (u • ε) = Eq.refl
  lemma-list-of-word2 (u • (w • v)) = Eq.cong (λ □ → u • □) (lemma-list-of-word2 (w • v))
  
  -- A wrapper around List.split3: split a list of words into 3 parts,
  -- where the first has length up to n and the second has length up
  -- to m.
  mysplit : ∀ {X} -> ℕ -> ℕ -> List (Word X) -> List X × Word X × List X
  mysplit n m us with split3 n m us
  ... | (xs , ys , zs) = (list-of-word (word-of-list2 xs) , word-of-list2 ys , list-of-word (word-of-list2 zs))
  
  -- Lemma: word-of-list2 respects concatenation of lists, up to associativity.
  lemma-append2 : ∀ {X Γ} (us ws : List (Word X)) -> Γ ⊢ word-of-list2 us • word-of-list2 ws === word-of-list2 (us ++ ws)
  lemma-append2 [] ws = left-unit
  lemma-append2 (u ∷ []) [] = right-unit
  lemma-append2 (u ∷ []) (w ∷ ws) = refl
  lemma-append2 (u ∷ u' ∷ us) ws =
    equational (u • word-of-list2 (u' ∷ us)) • word-of-list2 ws
            by assoc
        equals u • (word-of-list2 (u' ∷ us) • word-of-list2 ws)
            by right lemma-append2 (u' ∷ us) ws
        equals u • word-of-list2 (u' ∷ (us ++ ws))

  -- Lemma: Concatenating the output of mysplit is equivalent to the
  -- original word, up to associativity.
  lemma-mysplit : ∀ {X} {Γ : Context X} n m us {x y z} -> mysplit n m us ≡ (x , y , z) -> Γ ⊢ word-of-list x • y • word-of-list z === word-of-list2 us
  lemma-mysplit n m us {x} {y} {z} hyp =
    let s3 = split3 n m us
        xs = proj₁ s3
        ys = proj₁ (proj₂ s3)
        zs = proj₂ (proj₂ s3)
        hyp1 = Eq.cong proj₁ hyp
        hyp2 = Eq.cong proj₁ (Eq.cong proj₂ hyp)
        hyp3 = Eq.cong proj₂ (Eq.cong proj₂ hyp)
    in
    equational word-of-list x • y • word-of-list z
            by left refl' (Eq.cong word-of-list hyp1) reversed
        equals word-of-list (list-of-word (word-of-list2 xs)) • y • word-of-list z
            by left lemma-list-of-word (word-of-list2 xs) reversed
        equals word-of-list2 xs • y • word-of-list z
            by right right refl' (Eq.cong word-of-list hyp3) reversed
        equals word-of-list2 xs • y • word-of-list (list-of-word (word-of-list2 zs))
            by right right lemma-list-of-word (word-of-list2 zs) reversed
        equals word-of-list2 xs • y • word-of-list2 zs
            by right left refl' hyp2 reversed
        equals word-of-list2 xs • word-of-list2 ys • word-of-list2 zs
            by right lemma-append2 ys zs
        equals word-of-list2 xs • (word-of-list2 (ys ++ zs))
            by lemma-append2 xs (ys ++ zs)
        equals word-of-list2 (xs ++ ys ++ zs)
            by refl' (Eq.cong word-of-list2 (lemma-split3 n m us {xs} {ys} {zs} Eq.refl))
        equals word-of-list2 us

  -- The at-head tactic: apply an axiom or a lemma at the beginning of a
  -- list. See above for usage information.
  at-head : ∀ {X} {Γ : Context X} {u v k} -> Γ ⊢ u === v -> Γ ⊢ word-of-list (list-of-word u ++ k) === word-of-list (list-of-word v ++ k)
  at-head {X} {Γ} {u} {v} {k} hyp =
     equational word-of-list (list-of-word u ++ k)
             by lemma-append (list-of-word u) k reversed
         equals word-of-list (list-of-word u) • word-of-list k
             by left lemma-list-of-word u reversed
         equals u • word-of-list k
             by left hyp
         equals v • word-of-list k
             by left lemma-list-of-word v
         equals word-of-list (list-of-word v) • word-of-list k
             by lemma-append (list-of-word v) k
         equals word-of-list (list-of-word v ++ k)

  -- The in-context tactic: apply an axiom at a specified position
  -- inside a word. See above for usage information.
  in-context : ∀ {X} {Γ : Context X} {s t pre post s2 t2 s3 t3} -> (n m : ℕ) ->
             let s' = list-of-word2 s
                 t' = list-of-word2 t
                 m' = m + length t' ∸ length s'
             in (mysplit n m s' , mysplit n m' t' , list-of-word s2 , list-of-word t2) ≡ ((pre , s2 , post) , (pre , t2 , post) , list-of-word s3 , list-of-word t3) ->
                Γ ⊢ s3 === t3 -> Γ ⊢ s === t

  in-context {X} {Γ} {s} {t} {pre} {post} {s2} {t2} {s3} {t3} n m hyp lemma =
    let s' = list-of-word2 s
        t' = list-of-word2 t
        m' = m + length t' ∸ length s'
        hyp1 = Eq.cong proj₁ hyp
        hyp2 = Eq.cong proj₁ (Eq.cong proj₂ hyp)
        hyp3 = Eq.cong proj₁ (Eq.cong proj₂ (Eq.cong proj₂ hyp))
        hyp4 = Eq.cong proj₂ (Eq.cong proj₂ (Eq.cong proj₂ hyp))
    in
    equational s
            by refl' (lemma-list-of-word2 s) reversed
        equals word-of-list2 s'
            by lemma-mysplit n m s' hyp1 reversed
        equals word-of-list pre • s2 • word-of-list post
            by right left general-assoc hyp3
        equals word-of-list pre • s3 • word-of-list post
            by right left lemma
        equals word-of-list pre • t3 • word-of-list post
            by right left general-assoc hyp4 reversed
        equals word-of-list pre • t2 • word-of-list post
            by lemma-mysplit n m' t' hyp2
        equals word-of-list2 t'
            by refl' (lemma-list-of-word2 t)
        equals t

  -- The rewrite-in-context tactic: given a multistep rewrite rule,
  -- prove the equality of two words by applying rewriting only to the
  -- subword at the specified position. See above for usage information.
  rewrite-in-context : ∀ {X Γ s t pre post s2 t2} -> (multistep : (n : ℕ) -> List X -> List X) -> (lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)) -> (n m k : ℕ) ->
             let s' = list-of-word2 s
                 t' = list-of-word2 t
                 m' = m + length t' ∸ length s'
             in (mysplit n m s' , mysplit n m' t' , multistep k (list-of-word s2)) ≡ 
                ((pre , s2 , post) , (pre , t2 , post) , multistep k (list-of-word t2)) ->
                Γ ⊢ s === t
  rewrite-in-context {X} {Γ} {s} {t} {pre} {post} {s2} {t2} multistep lemma-multistep n m k hyp =
    let s' = list-of-word2 s
        t' = list-of-word2 t
        m' = m + length t' ∸ length s'
        hyp1 = Eq.cong proj₁ hyp
        hyp2 = Eq.cong proj₁ (Eq.cong proj₂ hyp)
        hyp3 = Eq.cong proj₂ (Eq.cong proj₂ hyp)
    in
    equational s
            by refl' (lemma-list-of-word2 s) reversed
        equals word-of-list2 s'
            by lemma-mysplit n m s' hyp1 reversed
        equals word-of-list pre • s2 • word-of-list post
            by right left lemma-list-of-word s2
        equals word-of-list pre • word-of-list (list-of-word s2) • word-of-list post
            by right left (lemma-multistep k (list-of-word s2))
        equals word-of-list pre • word-of-list (multistep k (list-of-word s2)) • word-of-list post
            by right left refl' (Eq.cong word-of-list hyp3)
        equals word-of-list pre • word-of-list (multistep k (list-of-word t2)) • word-of-list post
            by right left (lemma-multistep k (list-of-word t2)) reversed
        equals word-of-list pre • word-of-list (list-of-word t2) • word-of-list post
            by right left lemma-list-of-word t2 reversed
        equals word-of-list pre • t2 • word-of-list post
            by lemma-mysplit n m' t' hyp2
        equals word-of-list2 t'
            by refl' (lemma-list-of-word2 t)
        equals t


  rewrite-in-context' : ∀ {X Γ s t pre post s2 t2} -> (multistep : (n : ℕ) -> List X -> List X) -> (lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)) -> (n m m' k : ℕ) ->
             let s' = list-of-word2 s
                 t' = list-of-word2 t
                 -- m' = m + length t' ∸ length s'
             in (mysplit n m s' , mysplit n m' t' , multistep k (list-of-word s2)) ≡ 
                ((pre , s2 , post) , (pre , t2 , post) , (list-of-word t2)) ->
                Γ ⊢ s === t
  rewrite-in-context' {X} {Γ} {s} {t} {pre} {post} {s2} {t2} multistep lemma-multistep n m m' k hyp =
    let s' = list-of-word2 s
        t' = list-of-word2 t
        --m' = m + length t' ∸ length s'
        hyp1 = Eq.cong proj₁ hyp
        hyp2 = Eq.cong proj₁ (Eq.cong proj₂ hyp)
        hyp3 = Eq.cong proj₂ (Eq.cong proj₂ hyp)
    in
    equational s
            by refl' (lemma-list-of-word2 s) reversed
        equals word-of-list2 s'
            by lemma-mysplit n m s' hyp1 reversed
        equals word-of-list pre • s2 • word-of-list post
            by right left lemma-list-of-word s2
        equals word-of-list pre • word-of-list (list-of-word s2) • word-of-list post
            by right left (lemma-multistep k (list-of-word s2))
        equals word-of-list pre • word-of-list (multistep k (list-of-word s2)) • word-of-list post
            by right left refl' (Eq.cong word-of-list hyp3)
        equals word-of-list pre • word-of-list ((list-of-word t2)) • word-of-list post
            by right left lemma-list-of-word t2 reversed
        equals word-of-list pre • t2 • word-of-list post
            by lemma-mysplit n m' t' hyp2
        equals word-of-list2 t'
            by refl' (lemma-list-of-word2 t)
        equals t


-- ----------------------------------------------------------------------
-- * Some tactics for proofs by rewriting

module Rewriting
  where

  -- This module provides some tactics for proving equations between
  -- words by using a rewrite system. To use these tactics, a
  -- particular set of single-step rewrite rules must be supplied in
  -- the form of a Step-Function. The tactic general-rewrite in the
  -- submodule Step can be used to prove that two words are equal by
  -- rewriting them both to normal form. The tactic general-rewrite in
  -- the submodule Step-With-Standardization does the same, except it
  -- also applies a user-supplied standardization function before and
  -- after each rewrite step. This is typically used to implement
  -- rewriting up to commutativity.

  open Monoid-Equational
  open Associative

  infixl 4 _then_
  infixl 4 _then'_

  -- ----------------------------------------------------------------------
  -- ** Step functions

  -- The type for step functions. A step function inputs a word and
  -- outputs either nothing (if no rewrite rule can be applied), or
  -- else a new word (the result of applying a rewrite rule), together
  -- with a proof that the original word and the rewritten word are
  -- equivalent.  For efficiency, words are here implemented as lists
  -- of generators.
  Step-Function : (X : Set) -> (Γ : Context X) -> Set
  Step-Function X Γ = (xs : List X) -> Maybe (∃ λ (xs' : List X) -> Γ ⊢ word-of-list xs === word-of-list xs')


  infix 9 ⌈_
  infix 10 _⌉

  ⌈_ : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ₃ : Context (A ∪ B)} -> Step-Function A Γ₁ -> Step-Function (A ∪ B) (Γ₁ ⊹ Γ₂ ⊹ Γ₃)  
  (⌈ f) [] = nothing
  ⌈_ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(⌜ x ∷ xs) with lemma-take-while-isL-isL a
  ⌈_ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(⌜ x ∷ xs) | (l' , pr) with f l'
  ⌈_ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(⌜ x ∷ xs) | (l' , pr) | just (l'' , pr2) = just (map ⌜_ l'' ++ drop-while-isL a , d)
    where
      d : Γ₁ ⊹ Γ₂ ⊹ Γ₃ ⊢ [ ⌜ x ]ʷ • word-of-list xs === word-of-list (map ⌜_ l'' ++ drop-while-isL (⌜ x ∷ xs))
      d =
        equational [ ⌜ x ]ʷ • word-of-list xs
          by refl
        equals word-of-list a
          by refl' (Eq.cong word-of-list (lemma-take-drop-isL a)) reversed
        equals word-of-list (take-while-isL a ++ drop-while-isL a)
          by lemma-append (take-while-isL a) (drop-while-isL a) reversed
        equals word-of-list (take-while-isL a) • word-of-list (drop-while-isL a)
          by (left refl' (Eq.cong word-of-list (Eq.sym pr)))
        equals word-of-list (map ⌜_ l') • word-of-list (drop-while-isL a)
          by (left (lemma-⌞-map l' reversed))
        equals ⌞ word-of-list l' • word-of-list (drop-while-isL a)
          by (left ⌊ pr2)
        equals ⌞ word-of-list l'' • word-of-list (drop-while-isL a)
          by (left lemma-⌞-map l'')
        equals word-of-list (map ⌜_ l'') • word-of-list (drop-while-isL a)
          by lemma-append (map ⌜_ l'') (drop-while-isL (⌜ x ∷ xs))
        equals word-of-list (map ⌜_ l'' ++ drop-while-isL (⌜ x ∷ xs))
  ⌈_ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(⌜ x ∷ xs) | (l' , pr) | nothing = nothing
  (⌈ f) (x ⌝ ∷ xs) = nothing



  _⌉ : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ₃ : Context (A ∪ B)} -> Step-Function B Γ₂ -> Step-Function (A ∪ B) (Γ₁ ⊹ Γ₂ ⊹ Γ₃)  
  (_⌉ f) [] = nothing
  _⌉ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(x ⌝ ∷ xs) with lemma-take-while-isR-isR a
  _⌉ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(x ⌝ ∷ xs) | (l' , pr) with f l'
  _⌉ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(x ⌝ ∷ xs) | (l' , pr) | just (l'' , pr2) = just (map _⌝ l'' ++ drop-while-isR a , d)
    where
      d : Γ₁ ⊹ Γ₂ ⊹ Γ₃ ⊢ [ x ⌝ ]ʷ • word-of-list xs === word-of-list (map _⌝ l'' ++ drop-while-isR (x ⌝ ∷ xs))
      d =
        equational [ x ⌝ ]ʷ • word-of-list xs
          by refl
        equals word-of-list a
          by refl' (Eq.cong word-of-list (lemma-take-drop-isR a)) reversed
        equals word-of-list (take-while-isR a ++ drop-while-isR a)
          by lemma-append (take-while-isR a) (drop-while-isR a) reversed
        equals word-of-list (take-while-isR a) • word-of-list (drop-while-isR a)
          by (left refl' (Eq.cong word-of-list (Eq.sym pr)))
        equals word-of-list (map _⌝ l') • word-of-list (drop-while-isR a)
          by (left (lemma-⌟-map l' reversed))
        equals word-of-list l' ⌟ • word-of-list (drop-while-isR a)
          by (left pr2 ⌋)
        equals word-of-list l'' ⌟ • word-of-list (drop-while-isR a)
          by (left lemma-⌟-map l'')
        equals word-of-list (map _⌝ l'') • word-of-list (drop-while-isR a)
          by lemma-append (map _⌝ l'') (drop-while-isR (x ⌝ ∷ xs))
        equals word-of-list (map _⌝ l'' ++ drop-while-isR (x ⌝ ∷ xs))
  _⌉ {Γ₁ = Γ₁} {Γ₂} {Γ₃} f a@(x ⌝ ∷ xs) | (l' , pr) | nothing = nothing
  (_⌉ f) (⌜ x ∷ xs) = nothing


  lemma-lift-L' : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ₃ : Context (A ∪ B)} -> (n : ℕ) -> (f : List A -> List A) -> ((xs : List A) -> Γ₁ ⊢ word-of-list xs === word-of-list (f xs)) -> (zs : List (A ∪ B)) -> Γ₁ ⊹ Γ₂ ⊹ Γ₃ ⊢ word-of-list zs === word-of-list (lift-L' n f zs)
  lemma-lift-L' zero f pf zs = refl
  lemma-lift-L' (suc n) f pf [] = refl
  lemma-lift-L' (suc n) f pf (⌜ x ∷ zs) =
    equational [ ⌜ x ]ʷ • word-of-list zs
      by refl
    equals word-of-list (⌜ x ∷ zs)
      by refl' (Eq.cong word-of-list (lemma-take-drop-isL (⌜ x ∷ zs))) reversed
    equals word-of-list (take-while-isL (⌜ x ∷ zs) ++ drop-while-isL (⌜ x ∷ zs))
      by (lemma-append (⌜ x ∷ take-while-isL zs) (drop-while-isL zs) reversed)
    equals word-of-list (take-while-isL (⌜ x ∷ zs)) • word-of-list (drop-while-isL (⌜ x ∷ zs))
      by left refl' (Eq.cong word-of-list (proj₂ (lemma-take-while-isL-isL (⌜ x ∷ zs)))) reversed
    equals word-of-list (map ⌜_ (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))) • word-of-list (drop-while-isL (⌜ x ∷ zs))
      by left (lemma-⌞-map (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))  reversed)
    equals ⌞ word-of-list ((proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))) • word-of-list (drop-while-isL (⌜ x ∷ zs))
      by left ⌊ pf (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))
    equals ⌞ word-of-list (f (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))) • word-of-list (drop-while-isL (⌜ x ∷ zs))
      by (right lemma-lift-L' n f pf (drop-while-isL (⌜ x ∷ zs)))
    equals ⌞ word-of-list (f (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))) • word-of-list (lift-L' n f (drop-while-isL (⌜ x ∷ zs)))
      by (left lemma-⌞-map (f (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))))
    equals word-of-list (map ⌜_ (f (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs))))) • word-of-list (lift-L' n f (drop-while-isL (⌜ x ∷ zs)))
      by lemma-append ((map ⌜_ (f (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))))) (lift-L' n f (drop-while-isL (⌜ x ∷ zs)))
    equals word-of-list (map ⌜_ (f (proj₁ (lemma-take-while-isL-isL (⌜ x ∷ zs)))) ++ lift-L' n f (drop-while-isL (⌜ x ∷ zs)))
      by refl' (Eq.cong word-of-list Eq.refl)
    equals word-of-list (lift-L' (suc n) f (⌜ x ∷ zs))
  lemma-lift-L' (suc n) f pf (x ⌝ ∷ zs) = right lemma-lift-L' (suc n) f pf zs

  lemma-lift-L : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ₃ : Context (A ∪ B)} -> (f : List A -> List A) -> ((xs : List A) -> Γ₁ ⊢ word-of-list xs === word-of-list (f xs)) -> (zs : List (A ∪ B)) -> Γ₁ ⊹ Γ₂ ⊹ Γ₃ ⊢ word-of-list zs === word-of-list (lift-L f zs)
  lemma-lift-L f pf zs = lemma-lift-L' (length zs) f pf zs

  lemma-lift-R' : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ₃ : Context (A ∪ B)} -> (n : ℕ) -> (f : List B -> List B) -> ((xs : List B) -> Γ₂ ⊢ word-of-list xs === word-of-list (f xs)) -> (zs : List (A ∪ B)) -> Γ₁ ⊹ Γ₂ ⊹ Γ₃ ⊢ word-of-list zs === word-of-list (lift-R' n f zs)
  lemma-lift-R' zero f pf zs = refl
  lemma-lift-R' (suc n) f pf [] = refl
  lemma-lift-R' (suc n) f pf (_⌝ x ∷ zs) =
    equational [ _⌝ x ]ʷ • word-of-list zs
      by refl
    equals word-of-list (_⌝ x ∷ zs)
      by refl' (Eq.cong word-of-list (lemma-take-drop-isR (_⌝ x ∷ zs))) reversed
    equals word-of-list (take-while-isR (_⌝ x ∷ zs) ++ drop-while-isR (_⌝ x ∷ zs))
      by (lemma-append (_⌝ x ∷ take-while-isR zs) (drop-while-isR zs) reversed)
    equals word-of-list (take-while-isR (_⌝ x ∷ zs)) • word-of-list (drop-while-isR (_⌝ x ∷ zs))
      by left refl' (Eq.cong word-of-list (proj₂ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))) reversed
    equals word-of-list (map _⌝ (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))) • word-of-list (drop-while-isR (_⌝ x ∷ zs))
      by left (lemma-⌟-map (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))  reversed)
    equals word-of-list ((proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))) ⌟ • word-of-list (drop-while-isR (_⌝ x ∷ zs))
      by left pf (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs))) ⌋
    equals word-of-list (f (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))) ⌟ • word-of-list (drop-while-isR (_⌝ x ∷ zs))
      by (right lemma-lift-R' n f pf (drop-while-isR (_⌝ x ∷ zs)))
    equals word-of-list (f (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))) ⌟ • word-of-list (lift-R' n f (drop-while-isR (_⌝ x ∷ zs)))
      by (left lemma-⌟-map (f (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))))
    equals word-of-list (map _⌝ (f (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs))))) • word-of-list (lift-R' n f (drop-while-isR (_⌝ x ∷ zs)))
      by lemma-append ((map _⌝ (f (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))))) (lift-R' n f (drop-while-isR (_⌝ x ∷ zs)))
    equals word-of-list (map _⌝ (f (proj₁ (lemma-take-while-isR-isR (_⌝ x ∷ zs)))) ++ lift-R' n f (drop-while-isR (_⌝ x ∷ zs)))
      by refl' (Eq.cong word-of-list Eq.refl)
    equals word-of-list (lift-R' (suc n) f (_⌝ x ∷ zs))
    
  lemma-lift-R' (suc n) f pf (⌜ x ∷ zs) = right lemma-lift-R' (suc n) f pf zs

  lemma-lift-R : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ₃ : Context (A ∪ B)} -> (f : List B -> List B) -> ((xs : List B) -> Γ₂ ⊢ word-of-list xs === word-of-list (f xs)) -> (zs : List (A ∪ B)) -> Γ₁ ⊹ Γ₂ ⊹ Γ₃ ⊢ word-of-list zs === word-of-list (lift-R f zs)
  lemma-lift-R f pf zs = lemma-lift-R' (length zs) f pf zs


  Step-Function-n : ∀ {n} (X : ℕ -> Set) -> (Γ : Context (X n)) -> Set
  Step-Function-n {n} X Γ = (xs : List (X n)) -> Maybe (∃ λ (xs' : List (X n)) -> Γ ⊢ word-of-list xs === word-of-list xs')

  word-of-list' : ∀ {X} -> List (Word X) -> Word X
  word-of-list' xs = flatten-word (word-of-list xs)

  Step-Function-syllable : (X : Set) -> (Γ : Context X) -> Set
  Step-Function-syllable X Γ = (xs : List (Word X)) -> Maybe (∃ λ (xs' : List (Word X)) -> Γ ⊢ word-of-list' xs === word-of-list' xs')

  -- Sequentially combine two step functions. If the first step
  -- function successfully rewrites the word, use it; otherwise, use
  -- the second step function.
  _then_ : ∀ {X Γ} -> Step-Function X Γ -> Step-Function X Γ -> Step-Function X Γ
  (step1 then step2) xs with step1 xs
  ...                   | just res = just res
  ...                   | nothing = step2 xs

  _thenn_ : ∀ {n X Γ} -> Step-Function-n {n} X Γ -> Step-Function-n {n} X Γ -> Step-Function-n {n} X Γ
  (step1 thenn step2) xs with step1 xs
  ...                   | just res = just res
  ...                   | nothing = step2 xs

  _then'_ : ∀ {X Γ} -> Step-Function-syllable X Γ -> Step-Function-syllable X Γ -> Step-Function-syllable X Γ
  (step1 then' step2) xs with step1 xs
  ...                   | just res = just res
  ...                   | nothing = step2 xs

  -- Close a step function under congruence. In other words, input a
  -- step function that only rewrites the head of a list, and return a
  -- step function that rewrites anywhere within the list.
  step-cong : ∀ {X Γ} -> Step-Function X Γ -> Step-Function X Γ
  step-cong step [] = nothing
  step-cong step (h ∷ t) with step (h ∷ t)
  step-cong step (h ∷ t) | just res = just res
  step-cong step (h ∷ t) | nothing with step-cong step t
  step-cong step (h ∷ t) | nothing | just (t' , hyp) = just (h ∷ t' , (right hyp))
  step-cong step (h ∷ t) | nothing | nothing = nothing

  step-cong-n : ∀ {n X Γ} -> Step-Function-n {n} X Γ -> Step-Function-n {n} X Γ
  step-cong-n {n} {X} {Γ} step [] = nothing
  step-cong-n {n} {X} {Γ} step (h ∷ t) with step (h ∷ t)
  step-cong-n {n} {X} {Γ} step (h ∷ t) | just res = just res
  step-cong-n {n} {X} {Γ} step (h ∷ t) | nothing with step-cong-n {n} {X} {Γ} step t
  step-cong-n {n} {X} {Γ} step (h ∷ t) | nothing | just (t' , hyp) = just (h ∷ t' , (right hyp))
  step-cong-n {n} {X} {Γ} step (h ∷ t) | nothing | nothing = nothing

  step-cong' : ∀ {X Γ} -> Step-Function-syllable X Γ -> Step-Function-syllable X Γ
  step-cong' step [] = nothing
  step-cong' step (h ∷ t) with step (h ∷ t)
  step-cong' step (h ∷ t) | just res = just res
  step-cong' step (h ∷ t) | nothing with step-cong' step t
  step-cong' step (h ∷ t) | nothing | just (t' , hyp) = just (h ∷ t' , (right hyp))
  step-cong' step (h ∷ t) | nothing | nothing = nothing


  -- ----------------------------------------------------------------------
  -- ** Multistep rewriting

  module Step-syllable
         {X' : Set}
         {Γ : Context X'}
         (step : Step-Function-syllable X' Γ)
    where

    X = Word X'


    -- This module provides the tactic general-rewrite. Given a step
    -- function, this tactic can be used to prove that two words are
    -- equal by repeatedly applying the step function until the words
    -- are in normal form, then checking that they are equal.

    -- Users of this module typically specialize the module to a
    -- particular rewrite function. This can be done, for example, as
    -- follows:
    -- 
    -- module My-Rewrite = Rewriting.Step (step-cong my-stepfunction) renaming (general-rewrite to my-rewrite)
    --
    -- The tactic can then be used as follows:
    --
    -- open My-Rewrite
    -- property : Γ ⊢ A • B • C === D • E
    -- property = my-rewrite 100 auto

    open Presentation.Tactics.Lists.Strict

    -- Rewrite the given word until a normal form is reached, or up to
    -- a maximum of n rewrite steps. The parameter n is needed to
    -- ensure termination.
    multistep : (n : ℕ) -> List X -> List X
    multistep zero xs = xs
    multistep (suc n) xs with strict xs step
    multistep (suc n) xs | nothing = xs
    multistep (suc n) xs | just (xs' , _) = multistep n xs'

    -- Lemma: multistep rewriting returns an equivalent word.
    lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list' xs === word-of-list' (multistep n xs)
    lemma-multistep zero xs = refl
    lemma-multistep (suc n) xs with strict xs step in eq
    lemma-multistep (suc n) xs | nothing = refl
    lemma-multistep (suc n) xs | just (xs' , hyp) =
      equational word-of-list' xs
              by hyp
          equals word-of-list' xs'
              by lemma-multistep n xs'
          equals word-of-list' (multistep n xs')

    -- Return the entire rewrite sequence. This is useful for
    -- debugging rewriting strategies.
    multistep-trace : (n : ℕ) -> List X -> List (List X)
    multistep-trace zero xs = xs ∷ []
    multistep-trace (suc n) xs with step xs
    multistep-trace (suc n) xs | nothing = xs ∷ []
    multistep-trace (suc n) xs | just (xs' , _) = xs ∷ multistep-trace n xs'

    -- A tactic for proving equality of ground words based on a
    -- rewrite relation. The parameter n limits the number of rewrite
    -- steps applied, and is needed to ensure termination. If n is too
    -- small, the tactic may fail.
    general-rewrite : (n : ℕ) -> (p q : Word ⊤) -> {w u : Word X'} -> multistep n (list-of-word-special w p) ≡ multistep n (list-of-word-special u q) -> Γ ⊢ w === u
    general-rewrite n p q {w} {u} eq =
      let ws = list-of-word-special w p 
          us = list-of-word-special u q 
      in 
        equational w
                by lemma-list-of-word-special w p reversed
            equals word-of-list' ws
                by lemma-multistep n ws
            equals word-of-list' (multistep n ws)
                by refl' (Eq.cong word-of-list' eq)
            equals word-of-list' (multistep n us)
                by lemma-multistep n us reversed
            equals word-of-list' us
                by lemma-list-of-word-special u q
            equals u

  module Step
         {X : Set}
         {Γ : Context X}
         (step : Step-Function X Γ)
    where

    -- This module provides the tactic general-rewrite. Given a step
    -- function, this tactic can be used to prove that two words are
    -- equal by repeatedly applying the step function until the words
    -- are in normal form, then checking that they are equal.

    -- Users of this module typically specialize the module to a
    -- particular rewrite function. This can be done, for example, as
    -- follows:
    -- 
    -- module My-Rewrite = Rewriting.Step (step-cong my-stepfunction) renaming (general-rewrite to my-rewrite)
    --
    -- The tactic can then be used as follows:
    --
    -- open My-Rewrite
    -- property : Γ ⊢ A • B • C === D • E
    -- property = my-rewrite 100 auto

    open Presentation.Tactics.Lists.Strict

    -- Rewrite the given word until a normal form is reached, or up to
    -- a maximum of n rewrite steps. The parameter n is needed to
    -- ensure termination.
    multistep : (n : ℕ) -> List X -> List X
    multistep zero xs = xs
    multistep (suc n) xs with strict xs step
    multistep (suc n) xs | nothing = xs
    multistep (suc n) xs | just (xs' , _) = multistep n xs'

    -- Lemma: multistep rewriting returns an equivalent word.
    lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)
    lemma-multistep zero xs = refl
    lemma-multistep (suc n) xs with strict xs step in eq
    lemma-multistep (suc n) xs | nothing = refl
    lemma-multistep (suc n) xs | just (xs' , hyp) =
      equational word-of-list xs
              by hyp
          equals word-of-list xs'
              by lemma-multistep n xs'
          equals word-of-list (multistep n xs')

    -- Return the entire rewrite sequence. This is useful for
    -- debugging rewriting strategies.
    multistep-trace : (n : ℕ) -> List X -> List (List X)
    multistep-trace zero xs = xs ∷ []
    multistep-trace (suc n) xs with step xs
    multistep-trace (suc n) xs | nothing = xs ∷ []
    multistep-trace (suc n) xs | just (xs' , _) = xs ∷ multistep-trace n xs'

    -- A tactic for proving equality of ground words based on a
    -- rewrite relation. The parameter n limits the number of rewrite
    -- steps applied, and is needed to ensure termination. If n is too
    -- small, the tactic may fail.
    general-rewrite : (n : ℕ) -> {w u : Word X} -> multistep n (list-of-word w) ≡ multistep n (list-of-word u) -> Γ ⊢ w === u
    general-rewrite n {w} {u} eq =
      let ws = list-of-word w
          us = list-of-word u
      in 
        equational w
                by lemma-list-of-word w
            equals word-of-list ws
                by lemma-multistep n ws
            equals word-of-list (multistep n ws)
                by refl' (Eq.cong word-of-list eq)
            equals word-of-list (multistep n us)
                by lemma-multistep n us reversed
            equals word-of-list us
                by lemma-list-of-word u reversed
            equals u


    up-to-rewrite : (n : ℕ) -> {w u w' u' : Word X} -> (multistep n (list-of-word w) , multistep n (list-of-word u)) ≡ (list-of-word w' , list-of-word u') -> Γ ⊢ w' === u' -> Γ ⊢ w === u
    up-to-rewrite n {w} {u} {w'} {u'} eq der =
      let ws = list-of-word w
          us = list-of-word u
          hyp1 = Eq.cong proj₁ eq
          hyp2 = Eq.cong proj₂ eq          
      in 
        equational w
                by lemma-list-of-word w
            equals word-of-list ws
                by lemma-multistep n ws
            equals word-of-list (multistep n ws)
                by refl' (Eq.cong word-of-list hyp1)
            equals word-of-list (list-of-word w')
                by lemma-list-of-word w' reversed
            equals w'
                by der
            equals u'
                by lemma-list-of-word u'
            equals word-of-list (list-of-word u')
                by refl' (Eq.cong word-of-list hyp2) reversed
            equals word-of-list (multistep n us)
                by lemma-multistep n us reversed
            equals word-of-list us
                by lemma-list-of-word u reversed
            equals u


    -- Find the normal form for each element under a rewriting.
    normal-form : (n : ℕ) -> (w : Word X) -> ∃ λ (w' : Word X) -> Γ ⊢ w === w'
    normal-form n w = word-of-list (multistep n (list-of-word w)) , d1
      where
        d1 : Γ ⊢ w ===  word-of-list (multistep n (list-of-word w))
        d1 =
          equational w
            by lemma-list-of-word w
          equals word-of-list (list-of-word w)
            by lemma-multistep n (list-of-word w)
          equals word-of-list (multistep n (list-of-word w))
  
    open InContext
    
    rewrite-tactic : ∀ {s t pre post s2 t2} -> (n m k : ℕ) ->
               let s' = list-of-word2 s
                   t' = list-of-word2 t
                   m' = m + length t' ∸ length s'
               in (mysplit n m s' , mysplit n m' t' , multistep k (list-of-word s2)) ≡ 
                  ((pre , s2 , post) , (pre , t2 , post) , multistep k (list-of-word t2)) ->
                  Γ ⊢ s === t
    rewrite-tactic = rewrite-in-context multistep lemma-multistep

  -- ----------------------------------------------------------------------
  -- ** Multistep rewriting with standardization
  module Step-With-Standardization
         {X : Set}
         {Γ : Context X}
         (step : Step-Function X Γ)
         (standardize : List X -> List X)
         (lemma-standardize : (xs : List X) ->  Γ ⊢ word-of-list xs === word-of-list (standardize xs))
    where

    -- This module provides another version of the tactic
    -- general-rewrite that also applies a standardization function
    -- after each step. This is typically used to implement rewriting
    -- up to commutativity.
    --
    -- Users of this module typically specialize the module to a
    -- particular rewrite function and standardization function. This
    -- can be done, for example, as follows:
    --
    -- module My-Rewrite = Rewriting.Step (step-cong my-stepfunction) my-standardize my-lemma-standardize renaming (general-rewrite to my-rewrite)
    --
    -- The tactic can then be used as follows:
    --
    -- open My-Rewrite
    -- property : Γ ⊢ A • B • C === D • E
    -- property = my-rewrite 100 auto

    open Presentation.Tactics.Lists.Strict

    mutual
      -- Rewrite the given word until a normal form is reached, or up
      -- to a maximum of n rewrite steps. The parameter n is needed to
      -- ensure termination. The given standardization function is
      -- applied before and after every rewrite step.
      multistep : (n : ℕ) -> List X -> List X
      multistep n xs = multistep-st n (standardize xs)

      -- Auxiliary function: multistep-st assumes that the input is
      -- already standardized.
      multistep-st : (n : ℕ) -> List X -> List X
      multistep-st zero xs = xs
      multistep-st (suc n) xs with strict xs step
      multistep-st (suc n) xs | nothing = xs
      multistep-st (suc n) xs | just (xs' , _) = multistep n xs'

    mutual
      -- Lemma: multistep rewriting returns an equivalent word.
      lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)
      lemma-multistep n xs =
        let xs' = standardize xs
        in
          equational word-of-list xs
                  by lemma-standardize xs
              equals word-of-list xs'
                  by lemma-multistep-st n xs'
              equals word-of-list (multistep-st n xs')
                  by refl
              equals word-of-list (multistep n xs)

      lemma-multistep-st : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep-st n xs)
      lemma-multistep-st zero xs = refl
      lemma-multistep-st (suc n) xs with strict xs step in eq
      lemma-multistep-st (suc n) xs | nothing = refl
      lemma-multistep-st (suc n) xs | just (xs' , hyp) =
        equational word-of-list xs
                by hyp
            equals word-of-list xs'
                by lemma-multistep n xs'
            equals word-of-list (multistep n xs')

    -- Return the entire rewrite sequence. Useful for debugging
    -- rewriting strategies. Note: in the output, standardization
    -- steps will alternate with rewrite steps, even if the
    -- standardization is the identity.
    mutual
      multistep-trace : (n : ℕ) -> List X -> List (List X)
      multistep-trace n xs = xs ∷ multistep-trace-st n (standardize xs)

      multistep-trace-st : (n : ℕ) -> List X -> List (List X)
      multistep-trace-st zero xs = xs ∷ []
      multistep-trace-st (suc n) xs with step xs
      multistep-trace-st (suc n) xs | nothing = xs ∷ []
      multistep-trace-st (suc n) xs | just (xs' , _) = xs ∷ multistep-trace n xs'
  
    -- A tactic for proving equality of ground words based on a
    -- rewrite relation and a standardization function. The parameter
    -- n limits the number of rewrite steps applied, and is needed to
    -- ensure termination. If n is too small, the tactic may fail.
    general-rewrite : (n : ℕ) -> {w u : Word X} -> multistep n (list-of-word w) ≡ multistep n (list-of-word u) -> Γ ⊢ w === u
    general-rewrite n {w} {u} eq =
      let ws = list-of-word w
          us = list-of-word u
      in 
        equational w
                by lemma-list-of-word w
            equals word-of-list ws
                by lemma-multistep n ws
            equals word-of-list (multistep n ws)
                by refl' (Eq.cong word-of-list eq)
            equals word-of-list (multistep n us)
                by lemma-multistep n us reversed
            equals word-of-list us
                by lemma-list-of-word u reversed
            equals u




  -- ----------------------------------------------------------------------
  -- ** Multistep rewriting with standardization
  module Step-With-Standardization1
         {X : Set}
         {Γ : Context X}
         (step : Step-Function X Γ)
         (standardize : List X -> List X)
         (lemma-standardize : (xs : List X) ->  Γ ⊢ word-of-list xs === word-of-list (standardize xs))
    where

    -- This module provides another version of the tactic
    -- general-rewrite that also applies a standardization function
    -- after each step. This is typically used to implement rewriting
    -- up to commutativity.
    --
    -- Users of this module typically specialize the module to a
    -- particular rewrite function and standardization function. This
    -- can be done, for example, as follows:
    --
    -- module My-Rewrite = Rewriting.Step (step-cong my-stepfunction) my-standardize my-lemma-standardize renaming (general-rewrite to my-rewrite)
    --
    -- The tactic can then be used as follows:
    --
    -- open My-Rewrite
    -- property : Γ ⊢ A • B • C === D • E
    -- property = my-rewrite 100 auto

    open Presentation.Tactics.Lists.Strict

      -- Rewrite the given word until a normal form is reached, or up
      -- to a maximum of n rewrite steps. The parameter n is needed to
      -- ensure termination. The given standardization function is
      -- applied before and after every rewrite step.
    multistep : (n : ℕ) -> List X -> List X
    multistep zero xs = standardize xs
    multistep (suc k) xs with strict xs step
    multistep (suc k) xs | nothing = standardize xs
    multistep (suc k) xs | just (xs' , _) = multistep k xs'


    -- Lemma: multistep rewriting returns an equivalent word.
    lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)
    lemma-multistep zero xs = lemma-standardize xs
    lemma-multistep (suc k) xs with strict xs step in eq
    lemma-multistep (suc k) xs | nothing = lemma-standardize xs
    lemma-multistep (suc k) xs | just (xs' , hyp) =
      equational word-of-list xs
              by hyp
          equals word-of-list xs'
              by lemma-multistep k xs'
          equals word-of-list (multistep k xs')

    -- Return the entire rewrite sequence. This is useful for
    -- debugging rewriting strategies.
    multistep-trace : (n : ℕ) -> List X -> List (List X)
    multistep-trace zero xs = standardize xs ∷ []
    multistep-trace (suc k) xs with step xs
    multistep-trace (suc k) xs | nothing = standardize xs ∷ []
    multistep-trace (suc k) xs | just (xs' , _) = xs ∷ multistep-trace k xs'

    -- A tactic for proving equality of ground words based on a
    -- rewrite relation. The parameter n limits the number of rewrite
    -- steps applied, and is needed to ensure termination. If n is too
    -- small, the tactic may fail.
    general-rewrite : (n : ℕ) -> {w u : Word X} -> multistep n (list-of-word w) ≡ multistep n (list-of-word u) -> Γ ⊢ w === u
    general-rewrite k {w} {u} eq =
      let ws = list-of-word w
          us = list-of-word u
      in 
        equational w
                by lemma-list-of-word w
            equals word-of-list ws
                by lemma-multistep k ws
            equals word-of-list (multistep k ws)
                by refl' (Eq.cong word-of-list eq)
            equals word-of-list (multistep k us)
                by lemma-multistep k us reversed
            equals word-of-list us
                by lemma-list-of-word u reversed
            equals u



-- ----------------------------------------------------------------------
-- ** Conversion from equality to rewriting step


module Step-of-Equality
       {X' : Set}
       {Γ : Context X'}
       {{insX' : MaybeEq X'}}
  where
  open Rewriting
  open Associative
  open Monoid-Equational
  open import Presentation.Tactics.Lists using (split ; lemma-split)
  open Derivations using (MaybeEq-Word)

  X = Word X'

  
  step-of-rel : ∀ {u v} -> Γ ⊢ u === v -> Step-Function X' Γ
  step-of-rel {u} {v} uv gs with split (length (list-of-word u)) gs in eq | lemma-split (length (list-of-word u)) gs
  ... | x , x₂ | p with x =m? (list-of-word u)
  step-of-rel {u} {v} uv gs | x , x₂ | p | just x₁ = just (gs' , pr₂)
    where
      xs = list-of-word u
      xs' = list-of-word v
      gs' = list-of-word v ++ x₂
      pr0 : Γ ⊢ word-of-list xs === word-of-list xs'
      pr0 = equational word-of-list xs
        by lemma-list-of-word u reversed
        equals u
        by uv
        equals v
        by lemma-list-of-word v
        equals word-of-list xs'
      pr₁ : Γ ⊢ word-of-list xs' • word-of-list x₂ === word-of-list gs'
      pr₁ = lemma-append xs' x₂
      pr₂ : Γ ⊢ word-of-list gs === word-of-list gs'
      pr₂ rewrite  x₁ | eq | Eq.sym (p {xs} {x₂} _≡_.refl) =
        equational word-of-list (xs ++ x₂)
        by (lemma-append xs x₂ reversed)
        equals word-of-list xs • word-of-list x₂
        by cong pr0 refl
        equals word-of-list xs' • word-of-list x₂
        by lemma-append xs' x₂
        equals word-of-list gs'
  ... | nothing = nothing

  step-of-rel' : ∀ {u v} -> u === v ∈ Γ -> Step-Function X' Γ
  step-of-rel' x = step-of-rel (axiom x)

  step-syl-of-rel : ∀ (u v : Word (Word X')) -> Γ ⊢ flatten-word u === flatten-word v -> Step-Function-syllable X' Γ
  step-syl-of-rel u v rel gs with split (length (list-of-word u)) gs in eq | lemma-split (length (list-of-word u)) gs
  ... | x , x₂ | p with x =m? (list-of-word u)
  step-syl-of-rel u v rel gs | x , x₂ | p | just x₁ = just (gs' , pr₂)
    where
      xs = list-of-word u
      xs' = list-of-word v
      gs' = list-of-word v ++ x₂
      pr0 : Γ ⊢ flatten-word (word-of-list xs) === flatten-word (word-of-list xs')
      pr0 = equational flatten-word (word-of-list xs)
        by lemma-flatten-word (lemma-list-of-word u) reversed
        equals flatten-word u
        by rel
        equals flatten-word v
        by lemma-flatten-word (lemma-list-of-word v) 
        equals flatten-word (word-of-list xs')
      pr₁ : Γ ⊢ flatten-word (word-of-list xs') • flatten-word (word-of-list x₂) === flatten-word (word-of-list gs')
      pr₁ = lemma-append-syl xs' x₂
      pr₂ : Γ ⊢ flatten-word (word-of-list gs) === flatten-word (word-of-list gs')
      pr₂ rewrite  x₁ | eq | Eq.sym (p {xs} {x₂} _≡_.refl) =
        equational flatten-word (word-of-list (xs ++ x₂))
        by (lemma-append-syl xs x₂ reversed)
        equals flatten-word (word-of-list xs) • flatten-word (word-of-list x₂)
        by cong pr0 refl
        equals flatten-word (word-of-list xs') • flatten-word (word-of-list x₂)
        by lemma-append-syl xs' x₂
        equals flatten-word (word-of-list gs')
  ... | nothing = nothing

  sylstep-of-rel : ∀ {u v} -> (pl pr : Word ⊤) -> Γ ⊢ u === v -> Step-Function-syllable X' Γ
  sylstep-of-rel {u} {v} pl pr uv = step-syl-of-rel u' v' uv'
    where
      u' : Word (Word X')
      u' = word-of-list (list-of-word-special u pl)
      v' : Word (Word X')
      v' = word-of-list (list-of-word-special v pr)
      uv' : Γ ⊢ flatten-word u' === flatten-word v'
      uv' = equational
        flatten-word u'
        by lemma-list-of-word-special u pl
        equals u
        by uv
        equals v
        by lemma-list-of-word-special v pr reversed
        equals flatten-word v' 

-- ----------------------------------------------------------------------
-- * Some tactics for basis change.

module Basis-Change
       {X : Set}
       {Γ : Context X}
       (group-like : Grouplike Γ)
       (step : Rewriting.Step-Function X Γ)
  where

  open Associative
  open Monoid-Equational
  open Inverse X Γ group-like
  open Rewriting.Step (Rewriting.step-cong step)
  
  -- A simple tactic for proving an equation by doing a suitable basis
  -- change (i.e., conjugating the equation by a given word g).
  by-basis-change : ∀ {u v u' v'} -> (g : Word X) -> Γ ⊢ u === v -> (n : ℕ) -> (multistep n (list-of-word u') , multistep n (list-of-word (g • v • g ⁻¹))) ≡ (multistep n (list-of-word (g • u • g ⁻¹)) , multistep n (list-of-word v')) -> Γ ⊢ u' === v'
  by-basis-change {u} {v} {u'} {v'} g hyp n x =
    equational u'
            by general-rewrite n (Eq.cong proj₁ x)
        equals g • u • g ⁻¹
            by right left hyp
        equals g • v • g ⁻¹
            by general-rewrite n (Eq.cong proj₂ x)
        equals v'

open Associative

module Basis-Change-With-Standardization
       {X : Set}
       {Γ : Context X}
       (group-like : Grouplike Γ)
       (step : Rewriting.Step-Function X Γ)
       (standardize : List X -> List X)
       (lemma-standardize : (xs : List X) ->  Γ ⊢ word-of-list xs === word-of-list (standardize xs))
  where

  open Associative
  open Monoid-Equational
  open Inverse X Γ group-like
  open Rewriting.Step-With-Standardization (Rewriting.step-cong step) standardize lemma-standardize
  
  -- A simple tactic for proving an equation by doing a suitable basis
  -- change (i.e., conjugating the equation by a given word g).
  by-basis-change : ∀ {u v u' v'} -> (g : Word X) -> Γ ⊢ u === v -> (n : ℕ) -> (multistep n (list-of-word u) , multistep n (list-of-word (g • v' • g ⁻¹))) ≡ (multistep n (list-of-word (g • u' • g ⁻¹)) , multistep n (list-of-word v)) -> Γ ⊢ u' === v'
  by-basis-change {u} {v} {u'} {v'} g hyp n x =
    equational u'
            by symm (trans left-unit right-unit)
        equals ε • u' • ε
            by (left (lemma-left-inverse reversed))
        equals (g ⁻¹ • g) • u' • ε
            by (right right (lemma-left-inverse reversed))
        equals (g ⁻¹ • g) • u' • (g ⁻¹ • g)
            by special-assoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl
        equals g ⁻¹ • (g • u' • g ⁻¹) • g
            by right left general-rewrite n (Eq.cong proj₁ x) reversed
        equals g ⁻¹ • u • g
            by right left hyp
        equals g ⁻¹ • v • g
            by right left (general-rewrite n ((Eq.cong proj₂ x)) reversed)
        equals g ⁻¹ • (g • v' • g ⁻¹) • g
            by special-assoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl
        equals (g ⁻¹ • g) • v' • (g ⁻¹ • g)
            by (left lemma-left-inverse)
        equals ε • v' • (g ⁻¹ • g)
            by (right right lemma-left-inverse)
        equals ε • v' • ε
            by trans left-unit right-unit
        equals v'


module Basis-Change3
       {X : Set}
       {Γ : Context X}
       (group-like : Grouplike Γ)
       (step : Rewriting.Step-Function X Γ)
  where

  open Associative
  open Monoid-Equational
  open Inverse X Γ group-like
  open Rewriting.Step (Rewriting.step-cong step)
  
  -- A simple tactic for proving an equation by doing a suitable basis
  -- change (i.e., conjugating the equation by a given word g).
  by-basis-change : ∀ {u v u' v'} -> (g : Word X) -> Γ ⊢ u === v -> (n : ℕ) -> (multistep n (list-of-word u) , multistep n (list-of-word (g • v' • g ⁻¹))) ≡ (multistep n (list-of-word (g • u' • g ⁻¹)) , multistep n (list-of-word v)) -> Γ ⊢ u' === v'
  by-basis-change {u} {v} {u'} {v'} g hyp n x =
    equational u'
            by symm (trans left-unit right-unit)
        equals ε • u' • ε
            by (left (lemma-left-inverse reversed))
        equals (g ⁻¹ • g) • u' • ε
            by (right right (lemma-left-inverse reversed))
        equals (g ⁻¹ • g) • u' • (g ⁻¹ • g)
            by special-assoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl
        equals g ⁻¹ • (g • u' • g ⁻¹) • g
            by right left general-rewrite n (Eq.cong proj₁ x) reversed
        equals g ⁻¹ • u • g
            by right left hyp
        equals g ⁻¹ • v • g
            by right left (general-rewrite n ((Eq.cong proj₂ x)) reversed)
        equals g ⁻¹ • (g • v' • g ⁻¹) • g
            by special-assoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl
        equals (g ⁻¹ • g) • v' • (g ⁻¹ • g)
            by (left lemma-left-inverse)
        equals ε • v' • (g ⁻¹ • g)
            by (right right lemma-left-inverse)
        equals ε • v' • ε
            by trans left-unit right-unit
        equals v'



module Basis-Change2
       {X : Set}
       {Γ : Context X}
       (step : Rewriting.Step-Function X Γ)
  where

  open Associative
  open Monoid-Equational
  open Rewriting.Step (Rewriting.step-cong step)
  
  -- A simple tactic for proving an equation by doing a suitable basis
  -- change (i.e., conjugating the equation by a given word g).
  by-basis-change : ∀ {u v u' v'} -> (g g' : Word X) -> Γ ⊢ u === v -> (n : ℕ) -> (multistep n (list-of-word u') , multistep n (list-of-word (g • v • g'))) ≡ (multistep n (list-of-word (g • u • g')) , multistep n (list-of-word v')) -> Γ ⊢ u' === v'
  by-basis-change {u} {v} {u'} {v'} g g' hyp n x =
    equational u'
            by general-rewrite n (Eq.cong proj₁ x)
        equals g • u • g'
            by right left hyp
        equals g • v • g'
            by general-rewrite n (Eq.cong proj₂ x)
        equals v'

module Basis-Change-syllable
       {X' : Set}
       {Γ : Context X'}
--       (group-like : Grouplike Γ)
       (step : Rewriting.Step-Function-syllable X' Γ)
  where

  inv : Word ⊤ -> Word ⊤
  inv ([ x ]ʷ) = [ x ]ʷ
  inv ε = ε
  inv (w • w₁) = inv w₁ • inv w

  open Associative
  open Monoid-Equational
  open Rewriting.Step-syllable (Rewriting.step-cong' step)

  by-basis-change-syllable : ∀ {u v u' v'} ->
    (g : Word X') -> -- we use g on both side (g l g === g r g), implicitly assuming g is self-inverse. 
    (p : Word ⊤) ->
    Γ ⊢ u === v ->
    (n : ℕ) ->
    (pl pr pl' pr' : Word ⊤) ->
    multistep  n (list-of-word-special u' pl') ≡ multistep  n (list-of-word-special (g • u • g) (p • pl • p)) ->
    multistep  n (list-of-word-special (g • v • g) (p • pr • p)) ≡ multistep  n (list-of-word-special v' pr') ->
    Γ ⊢ u' === v'
  by-basis-change-syllable {u} {v} {u'} {v'} g p hyp n pl pr pl' pr' x y = 
    equational u'
            by general-rewrite  n pl' (p • pl • p) x
        equals g • u • g
            by right left hyp
        equals g • v • g
            by general-rewrite  n (p • pr • p) pr' y
        equals v'

  -- We might need a basis change like a l b ≡ a r b, where a /= b.
