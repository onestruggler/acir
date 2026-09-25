------------------------------------------------------------------------
-- Presentations of groups
--
-- PauliRotations: the Pauli rotation representation of Clifford+T
-- operators.  The 45-degree rotation R(P) about a 2-qubit Pauli operator P
-- is a Clifford conjugate of T; every Clifford+T operator is a product of
-- Pauli rotations followed by a Clifford operator.  Definitions,
-- commutativity and combination of rotations, sign corrections, and
-- tactics.  Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators" (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.PauliRotations where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_)
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
open import Examples.Groups.Clifford+T-2qubit.CliffordT-Lemmas as CliffordT-Lemmas
import Examples.Groups.Clifford+T-2qubit.Clifford-Lemmas as Clifford-Lemmas




private module C = Clifford+T

-- ----------------------------------------------------------------------
-- * Clifford operators

module Clifford where

  -- Here, we provide generators for the 2-qubit Clifford group (as
  -- opposed to the 2-qubit Clifford+T group, for which generators
  -- were defined in Generator.agda). It is convenient to have the
  -- Clifford generators as a separate entity because we will have to
  -- define their action on the Pauli operators.

  open Inverse-Clifford+T
  open Monoid-Equational

  -- Clifford generators (2 qubits).
  data Clifford : Set where
    CZ-gen : Clifford
    H0-gen : Clifford
    H1-gen : Clifford
    S0-gen : Clifford
    S1-gen : Clifford
    W-gen : Clifford

  -- Convenience definitions for singleton words.
  CZ : Word Clifford
  CZ = [ CZ-gen ]ʷ

  H0 : Word Clifford
  H0 = [ H0-gen ]ʷ

  H1 : Word Clifford
  H1 = [ H1-gen ]ʷ

  S0 : Word Clifford
  S0 = [ S0-gen ]ʷ

  S1 : Word Clifford
  S1 = [ S1-gen ]ʷ

  W : Word Clifford
  W = [ W-gen ]ʷ

  X0 : Word Clifford
  X0 = H0 • S0 • S0 • H0

  X1 : Word Clifford
  X1 = H1 • S1 • S1 • H1

  W⁻¹ : Word Clifford
  W⁻¹ = W ^ 7

  S0⁻¹ : Word Clifford
  S0⁻¹ = S0 ^ 3

  S1⁻¹ : Word Clifford
  S1⁻¹ = S1 ^ 3

  CX0 : Word Clifford
  CX0 = H0 • CZ • H0

  CX1 : Word Clifford
  CX1 = H1 • CZ • H1
      
  Swap : Word Clifford
  Swap = H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0

  -- Convert a Clifford generator to a Clifford+T generator.
  cliffordt-of-clifford-gen : Clifford -> Word C.Generator
  cliffordt-of-clifford-gen CZ-gen = C.CZ
  cliffordt-of-clifford-gen H0-gen = C.H0
  cliffordt-of-clifford-gen H1-gen = C.H1
  cliffordt-of-clifford-gen S0-gen = C.S0
  cliffordt-of-clifford-gen S1-gen = C.S1
  cliffordt-of-clifford-gen W-gen = C.W

  -- Convert a Clifford operator to a Clifford+T operator.
  cliffordt-of-clifford : Word Clifford -> Word C.Generator
  cliffordt-of-clifford ([ x ]ʷ) = cliffordt-of-clifford-gen x
  cliffordt-of-clifford ε = ε
  cliffordt-of-clifford (x • y) = cliffordt-of-clifford x • cliffordt-of-clifford y

  -- The inverse of a Clifford generator.
  inv-gen : Clifford -> Word Clifford
  inv-gen CZ-gen = CZ
  inv-gen H0-gen = H0
  inv-gen H1-gen = H1
  inv-gen S0-gen = S0⁻¹
  inv-gen S1-gen = S1⁻¹
  inv-gen W-gen = W⁻¹

  -- The inverse of a Clifford operator.
  inv : Word Clifford -> Word Clifford
  inv ([ x ]ʷ) = inv-gen x
  inv ε = ε
  inv (w • u) = inv u • inv w

  -- Lemma: inv-gen actually computes the inverse.
  lemma-inv-gen : (w : Clifford) -> C.Rel ⊢ cliffordt-of-clifford (inv-gen w) === (cliffordt-of-clifford-gen w) ⁻¹
  lemma-inv-gen CZ-gen = refl
  lemma-inv-gen H0-gen = refl
  lemma-inv-gen H1-gen = refl
  lemma-inv-gen S0-gen = refl
  lemma-inv-gen S1-gen = refl
  lemma-inv-gen W-gen = refl

  -- Lemma: inv actually computes the inverse.
  lemma-inv : (w : Word Clifford) -> C.Rel ⊢ cliffordt-of-clifford (inv w) === (cliffordt-of-clifford w) ⁻¹
  lemma-inv ([ x ]ʷ) = lemma-inv-gen x
  lemma-inv ε = refl
  lemma-inv (w • u) = cong (lemma-inv u) (lemma-inv w)

  -- Lemma: another way of saying that inv computes the inverse.
  lemma-C-inv : ∀ c -> C.Rel ⊢ cliffordt-of-clifford c • cliffordt-of-clifford (inv c) === ε
  lemma-C-inv c =
    equational cliffordt-of-clifford c • cliffordt-of-clifford (inv c)
            by right lemma-inv c
        equals cliffordt-of-clifford c • (cliffordt-of-clifford c) ⁻¹
            by lemma-right-inverse
        equals ε

-- ----------------------------------------------------------------------
-- * Pauli operators

module Pauli where

  -- Here, we provide a definition of the non-trivial signed 2-qubit
  -- Pauli operators. Note: for our purposes, we are not interested in
  -- the group structure of the Pauli group, but just on the action of
  -- the Clifford group on the Pauli operators. For this reason, we
  -- only consider the phases ±1 (and not ±i), and we also exclude the
  -- operators ±I⊗I, on which the Clifford group acts trivially.

  open Clifford
  open Finite
  open By-Cases

  -- ----------------------------------------------------------------------
  -- ** Definition of the Pauli operators

  -- Signs for Pauli operators: + and -.
  data Sign : Set where
    plus : Sign
    minus : Sign

  -- Negate a sign.
  neg-sign : Sign -> Sign
  neg-sign plus = minus
  neg-sign minus = plus

  -- The unsigned non-trivial 2-qubit Pauli operators. There are
  -- exactly 15 of them, and it is convenient to define them by
  -- enumerating them.
  data Unsigned-Pauli2 : Set where
    I⊗X : Unsigned-Pauli2
    I⊗Y : Unsigned-Pauli2
    I⊗Z : Unsigned-Pauli2
    X⊗I : Unsigned-Pauli2
    X⊗X : Unsigned-Pauli2
    X⊗Y : Unsigned-Pauli2
    X⊗Z : Unsigned-Pauli2
    Y⊗I : Unsigned-Pauli2
    Y⊗X : Unsigned-Pauli2
    Y⊗Y : Unsigned-Pauli2
    Y⊗Z : Unsigned-Pauli2
    Z⊗I : Unsigned-Pauli2
    Z⊗X : Unsigned-Pauli2
    Z⊗Y : Unsigned-Pauli2
    Z⊗Z : Unsigned-Pauli2

  -- A Pauli operator is a pair of a sign and an unsigned Pauli
  -- operator. In what follows, many definitions and lemmas are first
  -- given for the unsigned case, and then extended to the signed
  -- case. This has the advantage that our case distinctions usually
  -- have 15, rather than 30 cases.
  Pauli2 : Set
  Pauli2 = Sign × Unsigned-Pauli2

  -- Negate a Pauli operator.
  neg : Pauli2 -> Pauli2
  neg (sign , p) = (neg-sign sign , p)

  -- Lemma: double negation.
  lemma-neg-neg : {p : Pauli2} -> neg (neg p) ≡ p
  lemma-neg-neg {plus , p} = auto
  lemma-neg-neg {minus , p} = auto

  -- ----------------------------------------------------------------------
  -- ** Finiteness and equality

  -- Lemma: the set of non-trivial unsigned 2-qubit Pauli operators is
  -- finite. This can be used to automate certain case distinctions.
  lemma-finite-Unsigned-Pauli2 : Finite Unsigned-Pauli2
  lemma-finite-Unsigned-Pauli2 = (list , claim)
    where
      list = I⊗X ∷ I⊗Y ∷ I⊗Z ∷ X⊗I ∷ X⊗X ∷ X⊗Y ∷ X⊗Z ∷ Y⊗I ∷ Y⊗X ∷ Y⊗Y ∷ Y⊗Z ∷ Z⊗I ∷ Z⊗X ∷ Z⊗Y ∷ Z⊗Z ∷ []
      claim : ∀ x -> mem x list
      claim I⊗X = lemma-mem-nth 0 auto
      claim I⊗Y = lemma-mem-nth 1 auto
      claim I⊗Z = lemma-mem-nth 2 auto
      claim X⊗I = lemma-mem-nth 3 auto
      claim X⊗X = lemma-mem-nth 4 auto
      claim X⊗Y = lemma-mem-nth 5 auto
      claim X⊗Z = lemma-mem-nth 6 auto
      claim Y⊗I = lemma-mem-nth 7 auto
      claim Y⊗X = lemma-mem-nth 8 auto
      claim Y⊗Y = lemma-mem-nth 9 auto
      claim Y⊗Z = lemma-mem-nth 10 auto
      claim Z⊗I = lemma-mem-nth 11 auto
      claim Z⊗X = lemma-mem-nth 12 auto
      claim Z⊗Y = lemma-mem-nth 13 auto
      claim Z⊗Z = lemma-mem-nth 14 auto

  -- Lemma: the set of signs is finite.
  lemma-finite-Sign : Finite Sign
  lemma-finite-Sign = (list , claim)
    where
      list = plus ∷ minus ∷ []
      claim : ∀ x -> mem x list
      claim plus = mem-head
      claim minus = mem-tail mem-head

  -- Lemma: the set of (signed) 2-qubit Pauli operators is finite.
  lemma-finite-Pauli2 : Finite Pauli2
  lemma-finite-Pauli2 = lemma-finite-product lemma-finite-Sign lemma-finite-Unsigned-Pauli2

  -- Check equality of unsigned Pauli operators. This is used later in
  -- the semi-decision procedure for commutativity of R-syllables.
  unsigned-pauli2-equal? : (p q : Unsigned-Pauli2) -> Maybe (p ≡ q)
  unsigned-pauli2-equal? I⊗X I⊗X = just Eq.refl
  unsigned-pauli2-equal? I⊗Y I⊗Y = just Eq.refl
  unsigned-pauli2-equal? I⊗Z I⊗Z = just Eq.refl
  unsigned-pauli2-equal? X⊗I X⊗I = just Eq.refl
  unsigned-pauli2-equal? Y⊗I Y⊗I = just Eq.refl
  unsigned-pauli2-equal? Z⊗I Z⊗I = just Eq.refl
  unsigned-pauli2-equal? X⊗X X⊗X = just Eq.refl
  unsigned-pauli2-equal? X⊗Y X⊗Y = just Eq.refl
  unsigned-pauli2-equal? X⊗Z X⊗Z = just Eq.refl
  unsigned-pauli2-equal? Y⊗X Y⊗X = just Eq.refl
  unsigned-pauli2-equal? Y⊗Y Y⊗Y = just Eq.refl
  unsigned-pauli2-equal? Y⊗Z Y⊗Z = just Eq.refl
  unsigned-pauli2-equal? Z⊗X Z⊗X = just Eq.refl
  unsigned-pauli2-equal? Z⊗Y Z⊗Y = just Eq.refl
  unsigned-pauli2-equal? Z⊗Z Z⊗Z = just Eq.refl
  unsigned-pauli2-equal? _ _ = nothing

  -- ----------------------------------------------------------------------
  -- ** The action of the Clifford group on Pauli operators

  -- Definition: the action of each Clifford generator on each
  -- unsigned Pauli operator. In other words, given C and P, compute
  -- CPC⁻¹. This is a huge case distinction. The correctness of this
  -- definition is implicitly proved later, via the lemmas that it
  -- satisfies, and specifically lemma-R.
  pauli-action-gen-unsigned : Clifford -> Unsigned-Pauli2 -> Pauli2
  pauli-action-gen-unsigned CZ-gen I⊗X = (plus , Z⊗X)
  pauli-action-gen-unsigned CZ-gen I⊗Y = (plus , Z⊗Y)
  pauli-action-gen-unsigned CZ-gen I⊗Z = (plus , I⊗Z)
  pauli-action-gen-unsigned CZ-gen X⊗I = (plus , X⊗Z)
  pauli-action-gen-unsigned CZ-gen X⊗X = (plus , Y⊗Y)
  pauli-action-gen-unsigned CZ-gen X⊗Y = (minus , Y⊗X)
  pauli-action-gen-unsigned CZ-gen X⊗Z = (plus , X⊗I)
  pauli-action-gen-unsigned CZ-gen Y⊗I = (plus , Y⊗Z)
  pauli-action-gen-unsigned CZ-gen Y⊗X = (minus , X⊗Y)
  pauli-action-gen-unsigned CZ-gen Y⊗Y = (plus , X⊗X)
  pauli-action-gen-unsigned CZ-gen Y⊗Z = (plus , Y⊗I)
  pauli-action-gen-unsigned CZ-gen Z⊗I = (plus , Z⊗I)
  pauli-action-gen-unsigned CZ-gen Z⊗X = (plus , I⊗X)
  pauli-action-gen-unsigned CZ-gen Z⊗Y = (plus , I⊗Y)
  pauli-action-gen-unsigned CZ-gen Z⊗Z = (plus , Z⊗Z)
  pauli-action-gen-unsigned H0-gen I⊗X = (plus , I⊗X)
  pauli-action-gen-unsigned H0-gen I⊗Y = (plus , I⊗Y)
  pauli-action-gen-unsigned H0-gen I⊗Z = (plus , I⊗Z)
  pauli-action-gen-unsigned H0-gen X⊗I = (plus , Z⊗I)
  pauli-action-gen-unsigned H0-gen X⊗X = (plus , Z⊗X)
  pauli-action-gen-unsigned H0-gen X⊗Y = (plus , Z⊗Y)
  pauli-action-gen-unsigned H0-gen X⊗Z = (plus , Z⊗Z)
  pauli-action-gen-unsigned H0-gen Y⊗I = (minus , Y⊗I)
  pauli-action-gen-unsigned H0-gen Y⊗X = (minus , Y⊗X)
  pauli-action-gen-unsigned H0-gen Y⊗Y = (minus , Y⊗Y)
  pauli-action-gen-unsigned H0-gen Y⊗Z = (minus , Y⊗Z)
  pauli-action-gen-unsigned H0-gen Z⊗I = (plus , X⊗I)
  pauli-action-gen-unsigned H0-gen Z⊗X = (plus , X⊗X)
  pauli-action-gen-unsigned H0-gen Z⊗Y = (plus , X⊗Y)
  pauli-action-gen-unsigned H0-gen Z⊗Z = (plus , X⊗Z)
  pauli-action-gen-unsigned H1-gen X⊗I = (plus , X⊗I)
  pauli-action-gen-unsigned H1-gen Y⊗I = (plus , Y⊗I)
  pauli-action-gen-unsigned H1-gen Z⊗I = (plus , Z⊗I)
  pauli-action-gen-unsigned H1-gen I⊗X = (plus , I⊗Z)
  pauli-action-gen-unsigned H1-gen X⊗X = (plus , X⊗Z)
  pauli-action-gen-unsigned H1-gen Y⊗X = (plus , Y⊗Z)
  pauli-action-gen-unsigned H1-gen Z⊗X = (plus , Z⊗Z)
  pauli-action-gen-unsigned H1-gen I⊗Y = (minus , I⊗Y)
  pauli-action-gen-unsigned H1-gen X⊗Y = (minus , X⊗Y)
  pauli-action-gen-unsigned H1-gen Y⊗Y = (minus , Y⊗Y)
  pauli-action-gen-unsigned H1-gen Z⊗Y = (minus , Z⊗Y)
  pauli-action-gen-unsigned H1-gen I⊗Z = (plus , I⊗X)
  pauli-action-gen-unsigned H1-gen X⊗Z = (plus , X⊗X)
  pauli-action-gen-unsigned H1-gen Y⊗Z = (plus , Y⊗X)
  pauli-action-gen-unsigned H1-gen Z⊗Z = (plus , Z⊗X)
  pauli-action-gen-unsigned S0-gen I⊗X = (plus , I⊗X)
  pauli-action-gen-unsigned S0-gen I⊗Y = (plus , I⊗Y)
  pauli-action-gen-unsigned S0-gen I⊗Z = (plus , I⊗Z)
  pauli-action-gen-unsigned S0-gen X⊗I = (plus , Y⊗I)
  pauli-action-gen-unsigned S0-gen X⊗X = (plus , Y⊗X)
  pauli-action-gen-unsigned S0-gen X⊗Y = (plus , Y⊗Y)
  pauli-action-gen-unsigned S0-gen X⊗Z = (plus , Y⊗Z)
  pauli-action-gen-unsigned S0-gen Y⊗I = (minus , X⊗I)
  pauli-action-gen-unsigned S0-gen Y⊗X = (minus , X⊗X)
  pauli-action-gen-unsigned S0-gen Y⊗Y = (minus , X⊗Y)
  pauli-action-gen-unsigned S0-gen Y⊗Z = (minus , X⊗Z)
  pauli-action-gen-unsigned S0-gen Z⊗I = (plus , Z⊗I)
  pauli-action-gen-unsigned S0-gen Z⊗X = (plus , Z⊗X)
  pauli-action-gen-unsigned S0-gen Z⊗Y = (plus , Z⊗Y)
  pauli-action-gen-unsigned S0-gen Z⊗Z = (plus , Z⊗Z)
  pauli-action-gen-unsigned S1-gen X⊗I = (plus , X⊗I)
  pauli-action-gen-unsigned S1-gen Y⊗I = (plus , Y⊗I)
  pauli-action-gen-unsigned S1-gen Z⊗I = (plus , Z⊗I)
  pauli-action-gen-unsigned S1-gen I⊗X = (plus , I⊗Y)
  pauli-action-gen-unsigned S1-gen X⊗X = (plus , X⊗Y)
  pauli-action-gen-unsigned S1-gen Y⊗X = (plus , Y⊗Y)
  pauli-action-gen-unsigned S1-gen Z⊗X = (plus , Z⊗Y)
  pauli-action-gen-unsigned S1-gen I⊗Y = (minus , I⊗X)
  pauli-action-gen-unsigned S1-gen X⊗Y = (minus , X⊗X)
  pauli-action-gen-unsigned S1-gen Y⊗Y = (minus , Y⊗X)
  pauli-action-gen-unsigned S1-gen Z⊗Y = (minus , Z⊗X)
  pauli-action-gen-unsigned S1-gen I⊗Z = (plus , I⊗Z)
  pauli-action-gen-unsigned S1-gen X⊗Z = (plus , X⊗Z)
  pauli-action-gen-unsigned S1-gen Y⊗Z = (plus , Y⊗Z)
  pauli-action-gen-unsigned S1-gen Z⊗Z = (plus , Z⊗Z)
  pauli-action-gen-unsigned W-gen p⊗q = (plus , p⊗q)

  -- Extend the action to signed Pauli operators.
  -- Given C and P, compute CPC⁻¹.
  pauli-action-gen : Clifford -> Pauli2 -> Pauli2
  pauli-action-gen c (plus , p) = pauli-action-gen-unsigned c p
  pauli-action-gen c (minus , p) = neg (pauli-action-gen-unsigned c p)

  -- Extend the action to words of Clifford generators.
  pauli-action : Word Clifford -> Pauli2 -> Pauli2
  pauli-action ([ x ]ʷ) pauli = pauli-action-gen x pauli
  pauli-action ε pauli = pauli
  pauli-action (c • d) pauli = pauli-action c (pauli-action d pauli)

  -- Lemma: the Pauli action commutes with negation.
  lemma-pauli-action-neg : (c : Word Clifford) -> (p : Pauli2) -> pauli-action c (neg p) ≡ neg (pauli-action c p)
  lemma-pauli-action-neg ([ x ]ʷ) (plus , p) = Eq.refl
  lemma-pauli-action-neg ([ x ]ʷ) (minus , p) = lemma-neg-neg Eq.reversed
  lemma-pauli-action-neg ε p = Eq.refl
  lemma-pauli-action-neg (c • d) p =
     Eq.equational pauli-action c (pauli-action d (neg p))
             Eq.by Eq.cong (pauli-action c) (lemma-pauli-action-neg d p)
            equals pauli-action c (neg (pauli-action d p))
             Eq.by lemma-pauli-action-neg c (pauli-action d p)
            equals neg (pauli-action c (pauli-action d p))

  -- Lemma: The Pauli action of C⁻¹ is the inverse of that of C.
  lemma-pauli-action-inv : (c : Word Clifford) -> (p : Pauli2) -> pauli-action (c • inv c) p ≡ p
  lemma-pauli-action-inv ([ CZ-gen ]ʷ) p = equality-by-cases lemma-finite-Pauli2 p (λ p → (pauli-action (CZ • inv CZ) p , p)) auto
  lemma-pauli-action-inv ([ H0-gen ]ʷ) p = equality-by-cases lemma-finite-Pauli2 p (λ p → (pauli-action (H0 • inv H0) p , p)) auto
  lemma-pauli-action-inv ([ H1-gen ]ʷ) p = equality-by-cases lemma-finite-Pauli2 p (λ p → (pauli-action (H1 • inv H1) p , p)) auto
  lemma-pauli-action-inv ([ S0-gen ]ʷ) p = equality-by-cases lemma-finite-Pauli2 p (λ p → (pauli-action (S0 • inv S0) p , p)) auto
  lemma-pauli-action-inv ([ S1-gen ]ʷ) p = equality-by-cases lemma-finite-Pauli2 p (λ p → (pauli-action (S1 • inv S1) p , p)) auto
  lemma-pauli-action-inv ([ W-gen ]ʷ) p = equality-by-cases lemma-finite-Pauli2 p (λ p → (pauli-action (W • inv W) p , p)) auto
  lemma-pauli-action-inv ε p = Eq.refl
  lemma-pauli-action-inv (c • d) p =
    Eq.equational pauli-action c (pauli-action d (pauli-action (inv d) (pauli-action (inv c) p)))
            Eq.by Eq.cong (pauli-action c) (lemma-pauli-action-inv d (pauli-action (inv c) p))
           equals pauli-action c (pauli-action (inv c) p)
            Eq.by lemma-pauli-action-inv c p
           equals p

-- ----------------------------------------------------------------------
-- * Pauli rotation representation

module PauliRotRep where

  -- Here, we define the Pauli rotations and prove their main
  -- property. Specifically, for every non-trivial 2-qubit Pauli
  -- operator P, we define a word R(P), which we call an R-syllable.
  -- Mathematically, we have
  --
  -- R(P) = (1+ω)/2 I + (1-ω)/2 P,
  --
  -- but of course this is not the definition we give here, because we
  -- must define R(P) as a word in the Clifford+T generators.
  --
  -- The fundamental property of R-syllables is the following, which
  -- is essentially lemma-R below:
  --
  -- For any Clifford operator C, we have CR(P)C⁻¹ = R(CPC⁻¹).

  open Monoid-Equational
  open Associative
  open Clifford
  open Commuting-Clifford+T
  open Clifford-Lemmas
  open Commutes-T0
  open Pauli
  open Inverse-Clifford+T
  open Clifford+T-Duality

  -- ----------------------------------------------------------------------
  -- ** Conjugators

  -- The action of the Clifford group on Pauli operators is
  -- transitive. Specifically, for every 2-qubit Pauli operator P ≠ ±I,
  -- there exists some Clifford operator C such that
  --
  -- C(Z⊗I)C⁻¹ ≡ P.
  --
  -- For each P, we choose a particular such C and call it the
  -- conjugator of P.
  
  -- Definition: conjugators for the unsigned Pauli operators.
  conjugator-unsigned : Unsigned-Pauli2 -> Word Clifford
  conjugator-unsigned I⊗X = H1 • Swap
  conjugator-unsigned I⊗Y = S1 • H1 • Swap
  conjugator-unsigned I⊗Z = Swap
  conjugator-unsigned X⊗I = H0
  conjugator-unsigned X⊗X = H1 • CZ • H0
  conjugator-unsigned X⊗Y = S1 • H1 • CZ • H0
  conjugator-unsigned X⊗Z = CZ • H0
  conjugator-unsigned Y⊗I = S0 • H0
  conjugator-unsigned Y⊗X = H1 • S0 • CZ • H0
  conjugator-unsigned Y⊗Y = S1 • H1 • S0 • CZ • H0
  conjugator-unsigned Y⊗Z = S0 • CZ • H0
  conjugator-unsigned Z⊗I = ε
  conjugator-unsigned Z⊗X = H1 • H0 • CZ • H0
  conjugator-unsigned Z⊗Y = S1 • H1 • H0 • CZ • H0
  conjugator-unsigned Z⊗Z = H0 • CZ • H0

  -- Definition: conjugators for signed Pauli operators.
  conjugator : Pauli2 -> Word Clifford
  conjugator (plus , p⊗q) = conjugator-unsigned (p⊗q)
  conjugator (minus , p⊗q) = conjugator-unsigned (p⊗q) • X0

  -- Lemma (conjugators and negation): The conjugators for P and −P
  -- are related by an X0 gate.
  lemma-conjugator-neg : (p : Pauli2) -> C.Rel ⊢ cliffordt-of-clifford (conjugator (neg p)) === cliffordt-of-clifford (conjugator p) • C.X0
  lemma-conjugator-neg (plus , p) = refl
  lemma-conjugator-neg (minus , p) =
      equational cliffordt-of-clifford (conjugator (plus , p))
              by right-unit reversed
          equals cliffordt-of-clifford (conjugator (plus , p)) • ε
              by right rewrite-clifford 10 auto
          equals cliffordt-of-clifford (conjugator (plus , p)) • (C.X0 • C.X0)
              by assoc reversed
          equals (cliffordt-of-clifford (conjugator (plus , p)) • C.X0) • C.X0

  -- Lemma (the defining property of conjugators): C • (Z ⊗ I) • C⁻¹ ≡ P.
  -- Unsigned case.
  lemma-pauli-action-conjugator-unsigned : (p : Unsigned-Pauli2) -> pauli-action (conjugator-unsigned p) (plus , Z⊗I) ≡ (plus , p)
  lemma-pauli-action-conjugator-unsigned I⊗X = Eq.refl
  lemma-pauli-action-conjugator-unsigned I⊗Y = Eq.refl
  lemma-pauli-action-conjugator-unsigned I⊗Z = Eq.refl
  lemma-pauli-action-conjugator-unsigned X⊗I = Eq.refl
  lemma-pauli-action-conjugator-unsigned X⊗X = Eq.refl
  lemma-pauli-action-conjugator-unsigned X⊗Y = Eq.refl
  lemma-pauli-action-conjugator-unsigned X⊗Z = Eq.refl
  lemma-pauli-action-conjugator-unsigned Y⊗I = Eq.refl
  lemma-pauli-action-conjugator-unsigned Y⊗X = Eq.refl
  lemma-pauli-action-conjugator-unsigned Y⊗Y = Eq.refl
  lemma-pauli-action-conjugator-unsigned Y⊗Z = Eq.refl
  lemma-pauli-action-conjugator-unsigned Z⊗I = Eq.refl
  lemma-pauli-action-conjugator-unsigned Z⊗X = Eq.refl
  lemma-pauli-action-conjugator-unsigned Z⊗Y = Eq.refl
  lemma-pauli-action-conjugator-unsigned Z⊗Z = Eq.refl

  -- The defining property of conjugators, signed case.
  lemma-pauli-action-conjugator : (p : Pauli2) -> pauli-action (conjugator p) (plus , Z⊗I) ≡ p
  lemma-pauli-action-conjugator (plus , p) = lemma-pauli-action-conjugator-unsigned p
  lemma-pauli-action-conjugator (minus , p) =
    Eq.equational pauli-action (conjugator-unsigned p) (minus , Z⊗I)
            Eq.by lemma-pauli-action-neg (conjugator-unsigned p) (plus , Z⊗I)
           equals neg (pauli-action (conjugator-unsigned p) (plus , Z⊗I))
            Eq.by Eq.cong neg (lemma-pauli-action-conjugator-unsigned p)
           equals neg (plus , p)

  -- An alternative version of the previous lemma, where we act on
  -- ±Z⊗I instead of +Z⊗I.
  lemma-pauli-action-conjugator-alt : ∀ s p -> pauli-action (conjugator-unsigned p) (s , Z⊗I) ≡ (s , p)
  lemma-pauli-action-conjugator-alt plus p = lemma-pauli-action-conjugator-unsigned p
  lemma-pauli-action-conjugator-alt minus p =
   Eq.equational pauli-action c (minus , Z⊗I)
           Eq.by Eq.definition
          equals pauli-action c (neg (plus , Z⊗I))
           Eq.by lemma-pauli-action-neg c (plus , Z⊗I)
          equals neg (pauli-action c (plus , Z⊗I))
           Eq.by Eq.cong neg (lemma-pauli-action-conjugator-unsigned p)
          equals neg (plus , p)
           Eq.by Eq.definition
          equals (minus , p)
   where
     c = conjugator-unsigned p

  -- ----------------------------------------------------------------------
  -- ** R-syllables

  -- Definition of the R-syllables.
  R : Pauli2 -> Word C.Generator
  R pauli = cliffordt-of-clifford c • C.T0 • cliffordt-of-clifford c ⁻¹
    where
      c : Word Clifford
      c = conjugator pauli

  -- Special R-syllable: T0 = R(Z⊗I)
  lemma-R-T0 : C.Rel ⊢ C.T0 === R (plus , Z⊗I)
  lemma-R-T0 = general-assoc auto

  -- Special R-syllable: T1 = R(I⊗Z)
  lemma-R-T1 : C.Rel ⊢ C.T1 === R (plus , I⊗Z)
  lemma-R-T1 =
      equational C.T1
              by lemma-Swap-T0-Swap⁻¹ reversed
          equals C.Swap • C.T0 • C.Swap ⁻¹

  lemma-R-T0⁻¹ : Clifford+T.Rel ⊢ C.T0⁻¹ === R (plus , Z⊗I) • C.S0⁻¹
  lemma-R-T0⁻¹ =
    equational C.T0⁻¹
            by lemma-T0⁻¹
        equals C.T0 • C.S0 ^ 3
            by general-assoc auto
        equals R (plus , Z⊗I) • C.S0⁻¹

  lemma-R-T1⁻¹ : Clifford+T.Rel ⊢ C.T1⁻¹ === R (plus , I⊗Z) • C.S1⁻¹
  lemma-R-T1⁻¹ =
    equational C.T1⁻¹
            by lemma-T1⁻¹
        equals C.T1 • C.S1 ^ 3
            by general-assoc auto
        equals C.T1 • C.S1⁻¹
            by left lemma-R-T1
        equals R (plus , I⊗Z) • C.S1⁻¹

  -- ----------------------------------------------------------------------
  -- ** The fundamental property of R-syllables

  -- Our goal in this section is to prove the fundamental property of
  -- R-syllables, i.e., that for any Pauli operator P and Clifford
  -- operator C, we have
  --
  -- CR(P)C⁻¹ = R(CPC⁻¹).
  --
  -- Since both sets are finite, this could in principle be proved by
  -- a case distinction, but the number of Clifford operators is huge.
  -- Instead, we first prove some simpler lemmas about conjugators
  -- that will allow us to prove the fundamental property.


  -- A lemma about conjugators. This lemma is a bit obscure, but its
  -- merit is that it can be proved by case distinction with a
  -- relatively small number of cases: one case for each pair of a
  -- Clifford generator and an unsigned Pauli operator. The lemma
  -- relates the conjugator of P to the conjugator of CPC⁻¹.
  --
  -- Specifically, it states that if E is the conjugator of P and D is
  -- the conjugator of CPC⁻¹, then D⁻¹CE commutes with T0.
  lemma-conjugator-unsigned : (c : Clifford) -> (p : Unsigned-Pauli2) ->
      let D = cliffordt-of-clifford (conjugator (pauli-action-gen c (plus , p)))
          E = cliffordt-of-clifford (conjugator (plus , p))
          C = cliffordt-of-clifford-gen c
      in
          C.Rel ⊢ (D ⁻¹ • C • E) • C.T0 === C.T0 • (D ⁻¹ • C • E)
  lemma-conjugator-unsigned CZ-gen I⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen I⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen I⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen X⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen X⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen X⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen X⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Y⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Y⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Y⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Y⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Z⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Z⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Z⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned CZ-gen Z⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen I⊗X = general-comm-T0 140 auto
  lemma-conjugator-unsigned H0-gen I⊗Y = general-comm-T0 140 auto
  lemma-conjugator-unsigned H0-gen I⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen X⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen X⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen X⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen X⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Y⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Y⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Y⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Y⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Z⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Z⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Z⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned H0-gen Z⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen I⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen I⊗Y = general-comm-T0 220 auto
  lemma-conjugator-unsigned H1-gen I⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen X⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen X⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen X⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen X⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Y⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Y⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Y⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Y⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Z⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Z⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Z⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned H1-gen Z⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen I⊗X = general-comm-T0 190 auto
  lemma-conjugator-unsigned S0-gen I⊗Y = general-comm-T0 190 auto
  lemma-conjugator-unsigned S0-gen I⊗Z = general-comm-T0 200 auto
  lemma-conjugator-unsigned S0-gen X⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen X⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen X⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen X⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Y⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Y⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Y⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Y⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Z⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Z⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Z⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned S0-gen Z⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen I⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen I⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen I⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen X⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen X⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen X⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen X⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Y⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Y⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Y⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Y⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Z⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Z⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Z⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned S1-gen Z⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen I⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen I⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen I⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen X⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen X⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen X⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen X⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Y⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Y⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Y⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Y⊗Z = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Z⊗I = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Z⊗X = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Z⊗Y = general-comm-T0 130 auto
  lemma-conjugator-unsigned W-gen Z⊗Z = general-comm-T0 130 auto

  -- We extend the previous lemma to signed Pauli operators.
  lemma-conjugator : (c : Clifford) -> (p : Pauli2) ->
      let D = cliffordt-of-clifford (conjugator (pauli-action-gen c p))
          E = cliffordt-of-clifford (conjugator p)
          C = cliffordt-of-clifford-gen c
      in
          C.Rel ⊢ (D ⁻¹ • C • E) • C.T0 === C.T0 • (D ⁻¹ • C • E)

  lemma-conjugator c (plus , p) = lemma-conjugator-unsigned c p
  lemma-conjugator c (minus , p) =
      let D = cliffordt-of-clifford (conjugator (pauli-action-gen c (minus , p)))
          D' = cliffordt-of-clifford (conjugator (pauli-action-gen c (plus , p)))
          E = cliffordt-of-clifford (conjugator (minus , p))
          E' = cliffordt-of-clifford (conjugator (plus , p))
          C = cliffordt-of-clifford-gen c
 
          claim : C.Rel ⊢ D === D' • C.X0
          claim = lemma-conjugator-neg (pauli-action-gen c (plus , p))
      in
        equational (D ⁻¹ • C • E) • C.T0
                by left left lemma-cong-inv claim
            equals ((D' • C.X0) ⁻¹ • C • (E' • C.X0)) • C.T0
                by special-assoc (((□ • □) • □ • (□ • □)) • □) ((□ • □ • □ • □) • (□ • □)) auto
            equals (C.X0 ⁻¹ • D' ⁻¹ • C • E') • (C.X0 • C.T0)
                by right lemma-X0-T0
            equals (C.X0 ⁻¹ • D' ⁻¹ • C • E') • (C.T0 ⁻¹ • C.W • C.X0)
                by special-assoc ((□ • □ • □ • □) • (□ • □ • □)) (□ • ((□ • □ • □) • □) • (□ • □)) auto
            equals C.X0 ⁻¹ • ((D' ⁻¹ • C • E') • C.T0 ⁻¹) • (C.W • C.X0)
                by right left lemma-comm-inv (lemma-conjugator-unsigned c p)
            equals C.X0 ⁻¹ • (C.T0 ⁻¹ • (D' ⁻¹ • C • E')) • (C.W • C.X0)
                by special-assoc (□ • (□ • □) • (□ • □)) ((□ • □) • (□ • □) • □) auto
            equals (C.X0 ⁻¹ • C.T0 ⁻¹) • ((D' ⁻¹ • C • E') • C.W) • C.X0
                by right left Clifford.inclusion Clifford-Powers.lemma-comm-W reversed
            equals (C.X0 ⁻¹ • C.T0 ⁻¹) • (C.W • (D' ⁻¹ • C • E')) • C.X0
                by special-assoc ((□ • □) • (□ • (□ • □ • □)) • □) ((□ • □ • □) • □ • □ • □ • □) auto
            equals (C.X0 ⁻¹ • C.T0 ⁻¹ • C.W) • D' ⁻¹ • C • E' • C.X0
                by left lemma-T0-X0⁻¹ reversed
            equals (C.T0 • C.X0 ⁻¹) • D' ⁻¹ • C • E' • C.X0
                by general-assoc auto
            equals C.T0 • ((D' • C.X0) ⁻¹ • C • (E' • C.X0))
                by refl
            equals C.T0 • ((D' • C.X0) ⁻¹ • C • E)
                by right left lemma-cong-inv claim reversed
            equals C.T0 • (D ⁻¹ • C • E)
                
  -- Lemma: the fundamental property of R-syllables holds in the
  -- special case when C is a Clifford generator.
  lemma-R-gen : (c : Clifford) -> (p : Pauli2) -> C.Rel ⊢ cliffordt-of-clifford-gen c • R p === R (pauli-action-gen c p) • cliffordt-of-clifford-gen c
  lemma-R-gen c p =
    let D = cliffordt-of-clifford (conjugator (pauli-action-gen c p))
        E = cliffordt-of-clifford (conjugator p)
        C = cliffordt-of-clifford-gen c
    in
      equational C • (E • C.T0 • E ⁻¹)
              by special-assoc (□ • (□ • □ • □)) ((□ • □ • □) • □) auto
          equals (C • E • C.T0) • E ⁻¹
              by left left-unit reversed
          equals (ε • C • E • C.T0) • E ⁻¹
              by left left lemma-right-inverse reversed
          equals ((D • D ⁻¹) • C • E • C.T0) • E ⁻¹
              by special-assoc (((□ • □) • □ • □ • □) • □) (□ • ((□ • □ • □) • □) • □) auto
          equals D • ((D ⁻¹ • C • E) • C.T0) • E ⁻¹
              by right left lemma-conjugator c p
          equals D • (C.T0 • (D ⁻¹ • C • E)) • E ⁻¹
              by special-assoc (□ • (□ • (□ • □ • □)) • □) (((□ • □ • □) • □) • (□ • □)) auto
          equals ((D • C.T0 • D ⁻¹) • C) • (E • E ⁻¹)
              by right lemma-right-inverse
          equals ((D • C.T0 • D ⁻¹) • C) • ε
              by right-unit
          equals (D • C.T0 • D ⁻¹) • C

  -- The fundamental property of R-syllables.
  --
  -- Instead of CR(P)C⁻¹ = R(CPC⁻¹), we prove the equivalent property
  -- CR(P) = R(CPC⁻¹)C.
  --
  -- In other words, this lemma allows us to commute a Clifford
  -- operator past an R-syllable, resulting in a possibly different
  -- R-syllable.
  lemma-R : (c : Word Clifford) -> (p : Pauli2) -> C.Rel ⊢ cliffordt-of-clifford c • R p === R (pauli-action c p) • cliffordt-of-clifford c
  lemma-R ([ c ]ʷ) p = lemma-R-gen c p
  lemma-R ε p = trans left-unit (right-unit reversed)
  lemma-R (c • d) p =
      equational cliffordt-of-clifford (c • d) • R p
              by assoc
          equals cliffordt-of-clifford c • (cliffordt-of-clifford d • R p)
              by right lemma-R d p
          equals cliffordt-of-clifford c • (R (pauli-action d p) • cliffordt-of-clifford d)
              by assoc reversed
          equals (cliffordt-of-clifford c • R (pauli-action d p)) • cliffordt-of-clifford d
              by left lemma-R c (pauli-action d p)
          equals (R (pauli-action (c • d) p) • cliffordt-of-clifford c) • cliffordt-of-clifford d
              by assoc
          equals R (pauli-action (c • d) p) • cliffordt-of-clifford (c • d)

  -- The following lemma is a consequence of lemma-R, in a form that
  -- is convenient for the proofs of lemma-combine and
  -- lemma-correction below.
  lemma-action : ∀ c p s -> c ≡ conjugator-unsigned p -> Clifford+T.Rel ⊢ cliffordt-of-clifford c • R (s , Z⊗I) • (cliffordt-of-clifford c) ⁻¹ === R (s , p) 
  lemma-action c p s Eq.refl =
   equational d • R (s , Z⊗I) • d ⁻¹
           by assoc reversed
       equals (d • R (s , Z⊗I)) • d ⁻¹
           by left lemma-R c (s , Z⊗I)
       equals (R (pauli-action c (s , Z⊗I)) • d) • d ⁻¹
           by assoc
       equals R (pauli-action c (s , Z⊗I)) • (d • d ⁻¹)
           by right lemma-right-inverse
       equals R (pauli-action c (s , Z⊗I)) • ε
           by right-unit
       equals R (pauli-action c (s , Z⊗I))
           by refl' (Eq.cong R (lemma-pauli-action-conjugator-alt s p))
       equals R (s , p)
   where
     d = cliffordt-of-clifford c

-- ----------------------------------------------------------------------
-- * Commutativity of R-syllables.

module Commutativity where

  -- Here, we define a tactic tactic-pauli-commute for proving that
  -- two R-syllables commute. Most of the work of the tactic is done
  -- by a function comm-pauli that determines whether two R-syllables
  -- commute, and returns a proof of their commutativity if they do.
  -- Since commutativity must be proved from the Clifford+T axioms,
  -- there's a bit of work involved in doing so uniformly; this is
  -- achieved via a sequence of lemmas about properties of
  -- conjugators.

  open Monoid-Equational
  open Associative
  open Clifford
  open Commuting-Clifford+T
  open Pauli
  open PauliRotRep
  open Clifford-Lemmas

  -- For each unsigned Pauli operator P ≠ Z⊗I that commutes with Z⊗I,
  -- return a Clifford operator C such that:
  --
  -- (1) C (I⊗Z) C⁻¹ ≡ P
  --
  -- (2) C Z⊗I C⁻¹ ≡ Z⊗I.
  --
  -- Return nothing if P = Z⊗I or P doesn't commute with Z⊗I.
  -- 
  -- This function can be used, in conjunction with 'conjugator', to
  -- map any pair of commuting Pauli operators to (Z⊗I , I⊗Z).
  conjugator2-unsigned : (p : Unsigned-Pauli2) -> Maybe (∃ λ (c : Word Clifford) -> pauli-action c (plus , I⊗Z) ≡ (plus , p) × pauli-action c (plus , Z⊗I) ≡ (plus , Z⊗I))
  conjugator2-unsigned I⊗X = just (H1 , Eq.refl , Eq.refl)
  conjugator2-unsigned I⊗Y = just (S1 • H1 , Eq.refl , Eq.refl)
  conjugator2-unsigned I⊗Z = just (ε , Eq.refl , Eq.refl)
  conjugator2-unsigned Z⊗X = just (H1 • CX1 , Eq.refl , Eq.refl)
  conjugator2-unsigned Z⊗Y = just (S1 • H1 • CX1 , Eq.refl , Eq.refl)
  conjugator2-unsigned Z⊗Z = just (CX1 , Eq.refl , Eq.refl)
  conjugator2-unsigned _ = nothing

  -- Like conjugator2-unsigned, but for signed Pauli operators.
  conjugator2 : (p : Pauli2) -> Maybe (∃ λ (c : Word Clifford) -> pauli-action c (plus , I⊗Z) ≡ p × pauli-action c (plus , Z⊗I) ≡ (plus , Z⊗I))
  conjugator2 (plus , p) = conjugator2-unsigned p
  conjugator2 (minus , p) with conjugator2-unsigned p
  conjugator2 (minus , p) | nothing = nothing
  conjugator2 (minus , p) | just (c , eq1 , eq2) = just (c • X1 , claim1 , eq2)
    where
      claim1 : pauli-action (c • X1) (plus , I⊗Z) ≡ (minus , p)
      claim1 =
        Eq.equational pauli-action (c • X1) (plus , I⊗Z)
                Eq.by Eq.refl
               equals pauli-action c (neg (plus , I⊗Z))
                Eq.by lemma-pauli-action-neg c (plus , I⊗Z)
               equals neg (pauli-action c (plus , I⊗Z))
                Eq.by Eq.cong neg eq1
               equals neg (plus , p)
                Eq.by Eq.refl
               equals (minus , p)

  -- Given two commuting Pauli operators P and Q with P ≠ ±Q, return a
  -- Clifford operator C such that
  --
  -- (1) C (Z⊗I) C⁻¹ ≡ P
  --
  -- (2) C (I⊗Z) C⁻¹ ≡ Q.
  --
  -- If the operators don't commute, or if P = ±Q, return nothing.
  double-conjugator : (p q : Pauli2) -> Maybe (∃ λ (C : Word Clifford) -> pauli-action C (plus , Z⊗I) ≡ p × pauli-action C (plus , I⊗Z) ≡ q)
  double-conjugator p q with conjugator2 q'
    where
      d = conjugator p              -- D (Z⊗I) D⁻¹ ≡ P
      q' = pauli-action (inv d) q   -- D Q' D⁻¹ ≡ Q
  double-conjugator p q | nothing = nothing
  double-conjugator p q | just (e , eq1 , eq2)
                                    -- E (I⊗Z) E⁻¹ ≡ Q', E (Z⊗I) E⁻¹ ≡ Z⊗I
    = just (d • e , claim1 , claim2)
    where
      d = conjugator p            
      q' = pauli-action (inv d) q 

      claim1 : pauli-action (d • e) (plus , Z⊗I) ≡ p
      claim1 =
        Eq.equational pauli-action (d • e) (plus , Z⊗I)
                Eq.by Eq.refl
               equals pauli-action d (pauli-action e (plus , Z⊗I))
                Eq.by Eq.cong (pauli-action d) eq2
               equals pauli-action d (plus , Z⊗I)
                Eq.by lemma-pauli-action-conjugator p
               equals p

      claim2 : pauli-action (d • e) (plus , I⊗Z) ≡ q
      claim2 =
        Eq.equational pauli-action (d • e) (plus , I⊗Z)
                Eq.by Eq.refl
               equals pauli-action d (pauli-action e (plus , I⊗Z))
                Eq.by Eq.cong (pauli-action d) eq1
               equals pauli-action d q'
                Eq.by Eq.refl
               equals pauli-action (d • inv d) q
                Eq.by lemma-pauli-action-inv d q
               equals q

  -- A special case of commuting syllables is that R(Z⊗I) commutes with
  -- R(I⊗Z). This one case implies all other cases of commuting syllables
  -- P ≠ ±Q via conjugation.
  lemma-special-comm : C.Rel ⊢ R (plus , Z⊗I) • R (plus , I⊗Z) === R (plus , I⊗Z) • R (plus , Z⊗I)
  lemma-special-comm = 
      equational R (plus , Z⊗I) • R (plus , I⊗Z)
              by cong lemma-R-T0 lemma-R-T1 reversed
          equals C.T0 • C.T1
              by general-comm auto
          equals C.T1 • C.T0
              by cong lemma-R-T1 lemma-R-T0
          equals R (plus , I⊗Z) • R (plus , Z⊗I)

  -- Another special case of commuting syllables: R(Z⊗I) commutes with
  -- R(−Z⊗I).
  lemma-special-comm2 : C.Rel ⊢ R (plus , Z⊗I) • R (minus , Z⊗I) === R (minus , Z⊗I) • R (plus , Z⊗I)
  lemma-special-comm2 = 
      equational R (plus , Z⊗I) • R (minus , Z⊗I)
              by rewrite-clifford 10 auto
          equals (C.T0 • C.X0) • (C.T0 • C.X0)
              by axiom C.lemma-order-T0X0
          equals C.W
              by rewrite-clifford 10 auto
          equals C.X0 • C.W • C.X0
              by right left axiom C.lemma-order-T0X0 reversed
          equals C.X0 • ((C.T0 • C.X0) • (C.T0 • C.X0)) • C.X0
              by rewrite-clifford 10 auto
          equals C.X0 • C.T0 • C.X0 • C.T0
              by rewrite-clifford 10 auto
          equals R (minus , Z⊗I) • R (plus , Z⊗I)

  -- Every syllable R(P) commutes with R(−P).
  lemma-comm-plus-minus : ∀ p -> C.Rel ⊢ R (plus , p) • R (minus , p) === R (minus , p) • R (plus , p)
  lemma-comm-plus-minus p =
      equational R (plus , p) • R (minus , p)
              by cong (refl' (Eq.cong R claim1)) (refl' (Eq.cong R claim2))
          equals R r • R q
              by special-assoc □ (□ • ε) auto
          equals (R r • R q) • ε
              by right lemma-C-inv c reversed
          equals (R r • R q) • (cliffordt-of-clifford c • cliffordt-of-clifford (inv c))
              by special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto
          equals R r • (R q • cliffordt-of-clifford c) • cliffordt-of-clifford (inv c)
              by right left (lemma-R c (minus , Z⊗I)) reversed
          equals R r • (cliffordt-of-clifford c • R (minus , Z⊗I)) • cliffordt-of-clifford (inv c)
              by special-assoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto
          equals (R r • cliffordt-of-clifford c) • (R (minus , Z⊗I) • cliffordt-of-clifford (inv c))
              by left (lemma-R c (plus , Z⊗I)) reversed
          equals (cliffordt-of-clifford c • R (plus , Z⊗I)) • (R (minus , Z⊗I) • cliffordt-of-clifford (inv c))
              by special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto
          equals cliffordt-of-clifford c • (R (plus , Z⊗I) • R (minus , Z⊗I)) • cliffordt-of-clifford (inv c)
              by right left lemma-special-comm2
          equals cliffordt-of-clifford c • (R (minus , Z⊗I) • R (plus , Z⊗I)) • cliffordt-of-clifford (inv c)
              by special-assoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto
          equals (cliffordt-of-clifford c • R (minus , Z⊗I)) • (R (plus , Z⊗I) • cliffordt-of-clifford (inv c))
              by left (lemma-R c (minus , Z⊗I))
          equals (R q • cliffordt-of-clifford c) • (R (plus , Z⊗I) • cliffordt-of-clifford (inv c))
              by special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto
          equals R q • (cliffordt-of-clifford c • R (plus , Z⊗I)) • cliffordt-of-clifford (inv c)
              by right left (lemma-R c (plus , Z⊗I))
          equals R q • (R r • cliffordt-of-clifford c) • cliffordt-of-clifford (inv c)
              by special-assoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto
          equals (R q • R r) • (cliffordt-of-clifford c • cliffordt-of-clifford (inv c))
              by right lemma-C-inv c
          equals (R q • R r) • ε
              by special-assoc (□ • ε) □ auto
          equals R q • R r
              by cong (refl' (Eq.cong R claim2)) (refl' (Eq.cong R claim1)) reversed
          equals R (minus , p) • R (plus , p)
      where
        c = conjugator (plus , p)
        q = pauli-action c (minus , Z⊗I)
        r = pauli-action c (plus , Z⊗I)

        claim1 : (plus , p) ≡ r
        claim1 = lemma-pauli-action-conjugator-unsigned p Eq.reversed

        claim2 : (minus , p) ≡ q
        claim2 =
            Eq.equational (minus , p)
                    Eq.by Eq.definition
                   equals neg (plus , p)
                    Eq.by Eq.cong neg claim1
                   equals neg (pauli-action c (plus , Z⊗I))
                    Eq.by lemma-pauli-action-neg c (plus , Z⊗I) Eq.reversed
                   equals pauli-action c (minus , Z⊗I)
                    Eq.by Eq.definition
                   equals q

  -- A more general version of lemma-comm-plus-minus, stating that R(±P)
  -- commutes with R(±P), for each of the four combinations of "+" and
  -- "−".
  lemma-comm-self : ∀ s t p -> C.Rel ⊢ R (s , p) • R (t , p) === R (t , p) • R (s , p)
  lemma-comm-self plus plus p = refl
  lemma-comm-self plus minus p = lemma-comm-plus-minus p
  lemma-comm-self minus plus p = lemma-comm-plus-minus p reversed
  lemma-comm-self minus minus p = refl

  -- Determine whether (R p) and (R q) commute. If they commute,
  -- return a proof of this fact; otherwise, return nothing.
  comm-pauli : (p q : Pauli2) -> Maybe (commutes-word C.Rel (R p) (R q))
  comm-pauli p q with unsigned-pauli2-equal? (proj₂ p) (proj₂ q)
  comm-pauli (s , p) (t , .p) | just Eq.refl = just (lemma-comm-self s t p)
  comm-pauli p q | nothing with double-conjugator p q
  comm-pauli p q | nothing | nothing = nothing
  comm-pauli p q | nothing | just (c , eq1 , eq2) = just claim
    where
      p' = pauli-action c (plus , Z⊗I)
      q' = pauli-action c (plus , I⊗Z)

      claim : C.Rel ⊢ R p • R q === R q • R p
      claim =
        equational R p • R q
                by cong (refl' (Eq.cong R eq1)) (refl' (Eq.cong R eq2)) reversed
            equals R p' • R q'
                by special-assoc □ (□ • ε) auto
            equals (R p' • R q') • ε
                by right lemma-C-inv c reversed
            equals (R p' • R q') • (cliffordt-of-clifford c • cliffordt-of-clifford (inv c))
                by special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto
            equals R p' • (R q' • cliffordt-of-clifford c) • cliffordt-of-clifford (inv c)
                by right left (lemma-R c (plus , I⊗Z)) reversed
            equals R p' • (cliffordt-of-clifford c • R (plus , I⊗Z)) • cliffordt-of-clifford (inv c)
                by special-assoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto
            equals (R p' • cliffordt-of-clifford c) • (R (plus , I⊗Z) • cliffordt-of-clifford (inv c))
                by left (lemma-R c (plus , Z⊗I)) reversed
            equals (cliffordt-of-clifford c • R (plus , Z⊗I)) • (R (plus , I⊗Z) • cliffordt-of-clifford (inv c))
                by special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto
            equals cliffordt-of-clifford c • (R (plus , Z⊗I) • R (plus , I⊗Z)) • cliffordt-of-clifford (inv c)
                by right (left lemma-special-comm)
            equals cliffordt-of-clifford c • (R (plus , I⊗Z) • R (plus , Z⊗I)) • cliffordt-of-clifford (inv c)
                by special-assoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto
            equals (cliffordt-of-clifford c • R (plus , I⊗Z)) • (R (plus , Z⊗I) • cliffordt-of-clifford (inv c))
                by left (lemma-R c (plus , I⊗Z))
            equals (R q' • cliffordt-of-clifford c) • (R (plus , Z⊗I) • cliffordt-of-clifford (inv c))
                by special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto
            equals R q' • (cliffordt-of-clifford c • R (plus , Z⊗I)) • cliffordt-of-clifford (inv c)
                by right left (lemma-R c (plus , Z⊗I))
            equals R q' • (R p' • cliffordt-of-clifford c) • cliffordt-of-clifford (inv c)
                by special-assoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto
            equals (R q' • R p') • cliffordt-of-clifford c • cliffordt-of-clifford (inv c)
                by right lemma-C-inv c
            equals (R q' • R p') • ε
                by special-assoc (□ • ε) □ auto
            equals R q' • R p'
                by cong (refl' (Eq.cong R eq2)) (refl' (Eq.cong R eq1))
            equals R q • R p

  -- A tactic for proving that two R-syllables commute.
  tactic-pauli-commute : (p1 p2 : Pauli2) -> isJust (comm-pauli p1 p2) ≡ true -> C.Rel ⊢ R p1 • R p2 === R p2 • R p1
  tactic-pauli-commute p1 p2 = fromJust (comm-pauli p1 p2)

-- ----------------------------------------------------------------------
-- * Combining adjacent R-syllables.

module Combine where

  -- When two adjacent R-syllables use the same Pauli rotation
  -- (possibly with different signs), they can be combined into a
  -- Clifford operator. For example:
  --
  -- R(+Z⊗I) • R(-Z⊗I) = ω.
  --
  -- This module provides a function "combine", which given s, s', p,
  -- computes a Clifford operator c such that
  --
  -- R (s , p) • R (s' , p) === c.
  --
  -- It also provides a lemma "lemma-combine" that proves the above
  -- property.

  open Pauli
  open PauliRotRep
  open Monoid-Equational
  open Associative
  open Inverse-Clifford+T
  open Clifford using (cliffordt-of-clifford)
  open Clifford-Lemmas
  open Clifford+T

  -- A special case of combining adjacent syllables: Given s, s',
  -- return R (s , Z⊗I) • R (s', Z⊗I).
  combineZ0 : (s s' : Sign) -> Word Clifford+T.Generator
  combineZ0 plus plus = S0
  combineZ0 plus minus = W
  combineZ0 minus plus = W
  combineZ0 minus minus = S0⁻¹ • W ^ 2

  -- The defining property of combineZ0.
  lemma-combineZ0 : (s s' : Sign) -> Clifford+T.Rel ⊢ R (s , Z⊗I) • R (s' , Z⊗I) === combineZ0 s s'
  lemma-combineZ0 plus plus =
   equational R (plus , Z⊗I) • R (plus , Z⊗I)
           by general-assoc auto
       equals T0 • T0
           by axiom square-T0
       equals S0
  lemma-combineZ0 plus minus =
   equational R (plus , Z⊗I) • R (minus , Z⊗I)
           by general-assoc auto
       equals T0 • X0 • T0 • X0 ⁻¹
           by rewrite-clifford 100 auto
       equals (T0 • X0) • (T0 • X0)
           by axiom lemma-order-T0X0
       equals W
  lemma-combineZ0 minus plus =
   equational R (minus , Z⊗I) • R (plus , Z⊗I)
           by general-assoc auto
       equals X0 • T0 • X0 ⁻¹ • T0
           by rewrite-clifford 100 auto
       equals X0 • ((T0 • X0) • (T0 • X0)) • X0
           by right left axiom lemma-order-T0X0
       equals X0 • W • X0
           by rewrite-clifford 100 auto
       equals W
  lemma-combineZ0 minus minus =
   equational R (minus , Z⊗I) • R (minus , Z⊗I)
           by general-assoc auto
       equals X0 • T0 • X0 ⁻¹ • X0 • T0 • X0 ⁻¹
           by rewrite-clifford 100 auto
       equals X0 • (T0 • T0) • X0
           by right left axiom square-T0
       equals X0 • S0 • X0
           by rewrite-clifford 100 auto
       equals S0⁻¹ • W ^ 2

  -- Given s, s', p, compute w such that R (s , p) • R (s' , p) === w.
  combine : (s s' : Sign) -> (p : Unsigned-Pauli2) -> Word Clifford+T.Generator
  combine s s' p = c • corr • c ⁻¹
   where
     c = cliffordt-of-clifford (PauliRotRep.conjugator-unsigned p)
     corr = combineZ0 s s'

  -- The defining property of combine.
  lemma-combine : (s s' : Sign) -> (p : Unsigned-Pauli2) -> Clifford+T.Rel ⊢ R (s , p) • R (s' , p) === combine s s' p
  lemma-combine s s' p =
   equational R (s , p) • R (s' , p)
           by cong (lemma-action c' p s auto reversed) (lemma-action c' p s' auto reversed)
       equals (c • R (s , Z⊗I) • c ⁻¹) • (c • R (s' , Z⊗I) • c ⁻¹)
           by special-assoc ((□ • □ • □) • (□ • □ • □)) ((□ • □) • (□ • □) • (□ • □)) auto
       equals (c • R (s , Z⊗I)) • (c ⁻¹ • c) • (R (s' , Z⊗I) • c ⁻¹)
           by right left lemma-left-inverse
       equals (c • R (s , Z⊗I)) • ε • (R (s' , Z⊗I) • c ⁻¹)
           by special-assoc ((□ • □) • ε • (□ • □)) (□ • (□ • □) • □) auto
       equals c • (R (s , Z⊗I) • R (s' , Z⊗I)) • c ⁻¹
           by right left lemma-combineZ0 s s'
       equals c • corr • c ⁻¹
           by definition
       equals combine s s' p
   where
     c' = PauliRotRep.conjugator-unsigned p
     c = cliffordt-of-clifford c'
     corr = combineZ0 s s'

-- ----------------------------------------------------------------------
-- * Sign correction

module Correction where

  -- The R-syllables R(-P) and R(P) differ only by a Clifford operator:
  --
  -- R(-P) = R(P) • C.
  --
  -- In order to standardize the Pauli rotation representation as much
  -- as possible, it is desirable to do a "sign correction", i.e., to
  -- change all R-syllables to use positive signs.
  --
  -- This module provides a function "correction", which given any
  -- unsigned Pauli operator P, returns a Clifford operator C such
  -- that R(-P) = R(P) • C. It also provides a lemma
  -- "lemma-correction" proving the above property.

  open Pauli
  open Clifford using (cliffordt-of-clifford)
  open Clifford+T
  open Inverse-Clifford+T
  open PauliRotRep
  open Monoid-Equational
  open Associative
  open Clifford-Lemmas

  -- Given p, return a Clifford operator corr such that
  -- R (minus , p) === R (plus , p) • corr.
  correction : (p : Unsigned-Pauli2) -> Word Clifford+T.Generator
  correction p = c • S0⁻¹ • W • c ⁻¹
    where
      c' = PauliRotRep.conjugator-unsigned p
      c = cliffordt-of-clifford c'

  -- We first prove a special case of lemma-correction, when P = Z⊗I.
  lemma-correctionZ0 : Clifford+T.Rel ⊢ R (minus , Z⊗I) === R (plus , Z⊗I) • S0⁻¹ • W
  lemma-correctionZ0 =
    equational R (minus , Z⊗I)
            by general-assoc auto
        equals X0 • T0 • X0 ⁻¹
            by rewrite-clifford 10 auto
        equals (X0 • T0 • X0) • S0 • S0⁻¹
            by right left axiom square-T0 reversed
        equals (X0 • T0 • X0) • (T0 • T0) • S0⁻¹
            by rewrite-clifford 10 auto
        equals X0 • ((T0 • X0) • (T0 • X0)) • (X0 • T0 • S0⁻¹)
            by right left axiom lemma-order-T0X0
        equals X0 • W • (X0 • T0 • S0⁻¹)
            by rewrite-clifford 10 auto
        equals T0 • S0⁻¹ • W
            by general-assoc auto
        equals R (plus , Z⊗I) • S0⁻¹ • W

  -- The defining property of 'correction':
  lemma-correction : (p : Unsigned-Pauli2) -> Clifford+T.Rel ⊢ R (minus , p) === R (plus , p) • correction p
  lemma-correction p =
    equational R (minus , p)
            by lemma-action c' p minus auto reversed
        equals c • R (minus , Z⊗I) • c ⁻¹
            by right left lemma-correctionZ0
        equals c • (R (plus , Z⊗I) • S0⁻¹ • W) • c ⁻¹
            by special-assoc (□ • (□ • □ • □) • □) ((□ • □) • ε • (□ • □ • □)) auto
        equals (c • R (plus , Z⊗I)) • ε • (S0⁻¹ • W • c ⁻¹)
            by right left lemma-left-inverse reversed
        equals (c • R (plus , Z⊗I)) • (c ⁻¹ • c) • (S0⁻¹ • W • c ⁻¹)
            by special-assoc ((□ • □) • (□ • □) • (□ • □)) ((□ • □ • □) • (□ • □ • □)) auto
        equals (c • R (plus , Z⊗I) • c ⁻¹) • (c • S0⁻¹ • W • c ⁻¹)
            by definition
        equals (c • R (plus , Z⊗I) • c ⁻¹) • corr
            by left lemma-action c' p plus auto 
        equals R (plus , p) • corr
    where
      c' = PauliRotRep.conjugator-unsigned p
      c = cliffordt-of-clifford c'
      corr = correction p
