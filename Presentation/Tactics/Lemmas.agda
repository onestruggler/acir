------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemmas about judgements (from the Bian–Selinger Agda code, CC BY
-- 2.0): mapping generators, recognising words over one summand of a
-- sum of alphabets, simplifying derivations, and basic lemmas about
-- monoids and groups.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Presentation.Tactics.Lemmas where

open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (∃ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB
open import Presentation.GroupLike public using (Grouplike)
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_)

------------------------------------------------------------------------
-- Mapping generators

lemma-wmap : ∀ {A} {Γ : Context A} -> (f : A -> A) -> (∀ (a : A) -> Γ ⊢ [ a ]ʷ === [ f a ]ʷ) -> ∀ (w : Word A) -> Γ ⊢ w === wmap f w
lemma-wmap f pf ([ x ]ʷ) = pf x
lemma-wmap f pf ε = refl
lemma-wmap f pf (w • w₁) = cong (lemma-wmap f pf w) (lemma-wmap f pf w₁)


isL : ∀ {A B} -> (w : Word (A ∪ B)) -> Maybe (∃ λ (w' : Word A) -> ⌞ w' ≡ w)
isL ([ ⌜ x ]ʷ) = just (([ x ]ʷ) , Eq.refl)
isL ([ x ⌝ ]ʷ) = nothing
isL ε = just (ε , Eq.refl)
isL (w • v) with isL w | isL v
... | just (w' , pr1) | just (v' , pr2) = just ((w' • v') , Eq.cong₂ _•_ pr1 pr2)
... | _ | _ = nothing


isR : ∀ {A B} -> (w : Word (A ∪ B)) -> Maybe (∃ λ (w' : Word B) -> w' ⌟ ≡ w)
isR ([ ⌜ x ]ʷ) = nothing
isR ([ x ⌝ ]ʷ) = just (([ x ]ʷ) , Eq.refl)
isR ε = just (ε , Eq.refl)
isR (w • v) with isR w | isR v
... | just (w' , pr1) | just (v' , pr2) = just ((w' • v') , Eq.cong₂ _•_ pr1 pr2)
... | _ | _ = nothing

------------------------------------------------------------------------
-- Simplifying derivations

module Derivations where

  open Monoid-Equational

  infixl 4 _=W?_
  _=W?_ : ∀ {A} -> {{MaybeEq A}} -> (xs ys : Word A) -> Maybe (xs ≡ ys) 
  [ x ]ʷ =W? [ x₁ ]ʷ with x =m? x₁
  ... | just x₂ = just (Eq.cong [_]ʷ x₂)
  ... | nothing = nothing
  [ x ]ʷ =W? ε = nothing
  [ x ]ʷ =W? y • y₁ = nothing
  ε =W? [ x ]ʷ = nothing
  ε =W? ε = just Eq.refl
  ε =W? y • y₁ = nothing
  x • x₁ =W? [ x₂ ]ʷ = nothing
  x • x₁ =W? ε = nothing
  x • x₁ =W? y • y₁ with x =W? y | x₁ =W? y₁
  ... | just x₂ | just x₃ = just (Eq.cong₂ _•_ x₂ x₃)
  ... | just x₂ | nothing = nothing
  ... | nothing | h2 = nothing

  instance 
    MaybeEq-Word : ∀ {A} -> {{MaybeEq A}} -> MaybeEq (Word A)
    MaybeEq-Word ._=m?_ = _=W?_ 

  flatten-symm : ∀ {X : Set} {Γ : Context X} {l r} -> {{meq : MaybeEq X}} -> (n : ℕ) -> Γ ⊢ l === r -> Γ ⊢ l === r
  flatten-symm zero d = d
  flatten-symm (suc n) (trans d1 d2) = trans (flatten-symm n d1) (flatten-symm n d2)
  flatten-symm (suc n) (cong d1 d2) = cong (flatten-symm n d1) (flatten-symm n d2)
  flatten-symm (suc n) (symm refl) = refl
  flatten-symm (suc n) (symm (symm d)) = flatten-symm n d
  flatten-symm (suc n) (symm (trans d d₁)) = trans (flatten-symm n (symm d₁)) (flatten-symm n (symm d))
  flatten-symm (suc n) (symm (cong d d₁)) = cong (flatten-symm n (symm d)) (flatten-symm n (symm d₁))
  flatten-symm (suc n) (symm d) = symm d
  flatten-symm (suc n) d = d

  flatten-cong : ∀ {X : Set} {Γ : Context X} {l r} -> {{meq : MaybeEq X}} -> (n : ℕ) -> Γ ⊢ l === r -> Γ ⊢ l === r
  flatten-cong zero d = d
  flatten-cong (suc n) (trans d1 d2) = trans (flatten-cong n d1) (flatten-cong n d2)
  flatten-cong (suc n) (cong refl refl) = refl
  flatten-cong (suc n) (cong refl (cong refl d)) = trans (symm assoc) (trans (flatten-cong n (cong refl d)) assoc)
  flatten-cong (suc n) (cong (trans d0 d1) (trans d2 d3)) = trans (flatten-cong n (cong d0 d2)) (flatten-cong n (cong d1 d3))
  flatten-cong (suc n) (cong (trans d0 d1) d2) = trans (flatten-cong n (cong d0 d2)) (flatten-cong n (cong d1 refl))
  flatten-cong (suc n) (cong d1 (trans d2 d3)) = trans (flatten-cong n (cong d1 d2)) (flatten-cong n (cong refl d3))
  flatten-cong (suc n) (cong (cong d0 d1) (cong d2 d3)) = trans assoc (trans (flatten-cong n (cong d0 (cong d1 (cong d2 d3)))) (symm assoc))
  flatten-cong (suc n) (cong (cong d0 d1) d2) = trans assoc (trans (flatten-cong n (cong d0 (cong d1 d2))) (symm assoc))
  flatten-cong (suc n) (cong d1 (cong d2 d3)) with flatten-cong n (cong d2 d3)
  flatten-cong (suc n) (cong d1 (cong d2 d3)) | trans d4 d5 = trans (flatten-cong n (cong d1 d4)) (flatten-cong n (cong refl d5))
  flatten-cong (suc n) (cong d1 (cong d2 d3)) | cong d4 d5 with d4 | d1
  flatten-cong (suc n) (cong d1 (cong d2 d3)) | cong d4 d5 | refl | refl = trans (symm assoc) (trans (cong refl d5) assoc)
  flatten-cong (suc n) (cong d1 (cong d2 d3)) | cong d4 d5 | d4' | d1' = cong d1 (cong d4 d5)
  flatten-cong (suc n) (cong d1 (cong d2 d3)) | atom = cong d1 atom
  flatten-cong (suc n) (cong d1 d2) = cong d1 d2
  flatten-cong (suc n) d = d

  flatten-trans : ∀ {X : Set} {Γ : Context X} {l r} -> {{meq : MaybeEq X}} -> (n : ℕ) -> Γ ⊢ l === r -> Γ ⊢ l === r
  flatten-trans zero d = d
  -- testing
  flatten-trans (suc n) (cong d1 d2) = cong (flatten-trans n d1) (flatten-trans n d2)
  flatten-trans (suc n) (trans refl d) = flatten-trans n d
  flatten-trans (suc n) (trans d refl) = flatten-trans n d
  flatten-trans (suc n) (trans assoc (trans (symm assoc) d)) = flatten-trans n d
  flatten-trans (suc n) (trans (symm assoc) (trans assoc d)) = flatten-trans n d
  flatten-trans (suc n) (trans (trans d1 d2) d3) = flatten-trans n (trans d1 (trans d2 d3))
  flatten-trans (suc n) (trans d1 d2) = trans d1 (flatten-trans n d2)
  flatten-trans (suc n) d = d


  shorten-der1 : ∀ {X : Set} {Γ : Context X} {v t} -> {{meq : MaybeEq X}} -> (w : Word X) -> Γ ⊢ v === t -> Maybe (Γ ⊢ w === t)
  shorten-der1 {v = v} {t = t} w (axiom x) with w =m? t
  ... | just x₁ rewrite x₁ = just refl
  ... | nothing with w =m? v
  ... | nothing = nothing
  ... | just p rewrite p = just (axiom x)
  shorten-der1 {v = v} w refl with w =m? v
  ... | just x rewrite x = just refl
  ... | nothing = nothing
  shorten-der1 {v = v} {t = t} w (symm d) with w =m? t
  ... | just x₁ rewrite x₁ = just refl
  ... | nothing with w =m? v
  ... | nothing = nothing
  ... | just p rewrite p = just ((symm d))
  shorten-der1 w (PB.trans {w = v₁} {v = v} d d₁) with w =m? v₁
  ... | nothing = shorten-der1 w d₁
  ... | just x rewrite x = just (trans d d₁)
  shorten-der1 w (PB.cong {w = w₁} {w' = w'} {v = v} {v' = v'} d d₁) with w =m? w' • v'
  ... | just x rewrite x = just refl
  ... | nothing with w =m? w₁ • v
  ... | just x rewrite x = just (cong d d₁)
  ... | nothing = nothing
  shorten-der1 w (PB.assoc {w = w₁} {v = v} {u = u}) with w =m? (w₁ • v • u)
  ... | just x rewrite x = just refl
  ... | nothing with w =m? ((w₁ • v) • u)
  ... | just x rewrite x = just (assoc)
  ... | nothing = nothing
  shorten-der1 w (PB.left-unit {w = v}) with w =m? (ε • v)
  ... | just x rewrite x = just (left-unit)
  ... | nothing with w =m? v
  ... | just x rewrite x = just refl
  ... | nothing = nothing
  shorten-der1 {t = t} w (PB.right-unit {w = v}) with w =m? (v • ε)
  ... | just x rewrite x = just (right-unit)
  ... | nothing with w =m? v
  ... | just x rewrite x = just refl
  ... | nothing = nothing


  shorten-der1s : ∀ {X : Set} {Γ : Context X} {v t} -> {{meq : MaybeEq X}} -> (n : ℕ) -> (w : Word X) -> Γ ⊢ v === t -> Maybe (Γ ⊢ w === t)
  shorten-der1s zero w d = nothing
  shorten-der1s (suc n) w d with shorten-der1 w d
  shorten-der1s (suc n) w d | just (trans s1 s2) with shorten-der1s n w s2
  shorten-der1s (suc n) w d | just (trans s1 s2) | just x = just x
  shorten-der1s (suc n) w d | just (trans s1 s2) | nothing = just (trans s1 s2)
  shorten-der1s (suc n) w d | just x = just x
  shorten-der1s (suc n) w d | nothing = nothing


  shorten-der : ∀ {X : Set} {Γ : Context X} {s t} -> {{meq : MaybeEq X}} -> (n : ℕ) -> Γ ⊢ s === t -> (Γ ⊢ s === t)
  shorten-der zero d = d
  shorten-der {s = s} {t} (suc n) (PB.trans {v = v} d d₁) with shorten-der1s (suc n) v d₁
  shorten-der {s = s} {t} (suc n) (PB.trans {v = v} d d₁) | just x with shorten-der n d 
  shorten-der {s = s} {t} (suc n) (PB.trans {v = v} d d₁) | just x | refl = (shorten-der n (flatten-trans 10000 x))
  shorten-der {s = s} {t} (suc n) (PB.trans {v = v} d d₁) | just x | d' = trans d' (shorten-der n (flatten-trans 10000 x))
  shorten-der {s = s} {t} (suc n) (PB.trans {v = v} d d₁) | nothing with shorten-der n d
  shorten-der {s = s} {t} (suc n) (PB.trans {v = v} d d₁) | nothing | refl = (shorten-der n d₁)
  shorten-der {s = s} {t} (suc n) (PB.trans {v = v} d d₁) | nothing | d' = trans d' (shorten-der n d₁)
  -- testing
  shorten-der n (cong d1 d2) = cong (shorten-der n d1) (shorten-der n d2)
  shorten-der n d = d

  simplify-der : ∀ {X : Set} {Γ : Context X} {l r} -> {{meq : MaybeEq X}} -> (n : ℕ) -> Γ ⊢ l === r -> Γ ⊢ l === r
  simplify-der zero d = d
  simplify-der n d = shorten-der n (flatten-trans 10000 (flatten-cong 10 (flatten-symm 10000 d )))


-- ----------------------------------------------------------------------
-- * Basic lemmas about monoids

------------------------------------------------------------------------
-- Basic lemmas about monoids

-- We take X and Γ to be fixed throughout the following lemmas.
module Monoid-Lemmas {X : Set} {Γ : Context X} where

  open Monoid-Equational

  -- The left unit is unique.
  lemma-left-unit-unique : {w : Word X} -> (∀ v -> Γ ⊢ w • v === v) -> Γ ⊢ w === ε
  lemma-left-unit-unique {w} p =
    equational w
            by right-unit reversed
        equals w • ε
            by p ε
        equals ε

  -- The right unit is unique.
  lemma-right-unit-unique : {w : Word X} -> (∀ v -> Γ ⊢ v • w === v) -> Γ ⊢ w === ε
  lemma-right-unit-unique {w} p =
    equational w
            by left-unit reversed
        equals ε • w
            by p ε
        equals ε

  -- Congruence for powers.
  lemma-cong-power : {w v : Word X} (n : ℕ) -> Γ ⊢ w === v -> Γ ⊢ w ^ n === v ^ n
  lemma-cong-power zero hyp = refl
  lemma-cong-power (suc zero) hyp = hyp
  lemma-cong-power (suc (suc n)) hyp = cong hyp (lemma-cong-power (suc n) hyp)

  -- Recursive expansion of powers by repeated multiplication on the left.
  lemma-power-suc-left : {w : Word X} (n : ℕ) -> Γ ⊢ w ^ (suc n) === w • w ^ n
  lemma-power-suc-left zero = right-unit reversed
  lemma-power-suc-left (suc n) = refl

  -- Recursive expansion of powers by repeated multiplication on the right.
  lemma-power-suc-right : {w : Word X} (n : ℕ) -> Γ ⊢ w ^ (suc n) === w ^ n • w
  lemma-power-suc-right zero = left-unit reversed
  lemma-power-suc-right {w} (suc n) =
      equational w • w ^ suc n
              by right lemma-power-suc-right n
          equals w • (w ^ n • w)
              by assoc reversed
          equals (w • w ^ n) • w
              by left lemma-power-suc-left n reversed
          equals w ^ (suc n) • w

  -- A lemma about powers and multiplication.
  lemma-comm-power : ∀ {v w' w} -> (n : ℕ) -> Γ ⊢ v • w === w' • v -> Γ ⊢ v • w ^ n === w' ^ n • v
  lemma-comm-power {v} {w'} {w} zero hyp =
      equational v • ε
              by right-unit
          equals v
              by left-unit reversed
          equals ε • v
  lemma-comm-power {v} {w'} {w} (suc n) hyp =
      equational v • w ^ suc n
              by right lemma-power-suc-left n
          equals v • (w • w ^ n)
              by assoc reversed
          equals (v • w) • w ^ n
              by left hyp
          equals (w' • v) • w ^ n
              by assoc
          equals w' • (v • w ^ n)
              by right lemma-comm-power n hyp
          equals w' • (w' ^ n • v)
              by assoc reversed
          equals (w' • w' ^ n) • v
              by left lemma-power-suc-left n reversed
          equals w' ^ suc n • v

  -- Commutativity of powers.
  lemma-comm-powers : ∀ {w v} -> (n m : ℕ) -> Γ ⊢ w • v === v • w -> Γ ⊢ w ^ n • v ^ m === v ^ m • w ^ n
  lemma-comm-powers n m hyp = lemma-comm-power n (lemma-comm-power m hyp reversed) reversed

  -- Powers of products.
  lemma-product-power : ∀ {w v} -> (n : ℕ) -> Γ ⊢ w • v === v • w -> Γ ⊢ (w • v) ^ n === w ^ n • v ^ n
  lemma-product-power zero hyp = right-unit reversed
  lemma-product-power {w} {v} (suc n) hyp =
      equational (w • v) ^ suc n
              by lemma-power-suc-left n
          equals (w • v) • (w • v) ^ n
              by right lemma-product-power n hyp
          equals (w • v) • (w ^ n • v ^ n)
              by assoc
          equals w • (v • (w ^ n • v ^ n))
              by right assoc reversed
          equals w • (v • w ^ n) • v ^ n
              by right left lemma-comm-power n (hyp reversed)
          equals w • (w ^ n • v) • v ^ n
              by right assoc
          equals w • (w ^ n • (v • v ^ n))
              by assoc reversed
          equals (w • w ^ n) • (v • v ^ n)
              by cong (lemma-power-suc-left n) (lemma-power-suc-left n) reversed
          equals w ^ suc n • v ^ suc n
  

  -- Power and change of basis.
  lemma-basis-change : ∀ {w w' v} -> (n : ℕ) -> Γ ⊢ w' • w === ε -> Γ ⊢ (w • v • w') ^ suc n === w • v ^ suc n • w'
  lemma-basis-change {w} {w'} {v} 0 hyp = refl
  lemma-basis-change {w} {w'} {v} (suc n) hyp =
    equational (w • v • w') ^ suc (suc n)
            by definition
        equals (w • v • w') • (w • v • w') ^ suc n
            by right (lemma-basis-change n hyp)
        equals (w • v • w') • w • v ^ suc n • w'
            by left assoc reversed
        equals ((w • v) • w') • w • v ^ suc n • w'
            by assoc reversed
        equals (((w • v) • w') • w) • v ^ suc n • w'
            by left assoc
        equals ((w • v) • (w' • w)) • v ^ suc n • w'
            by left right hyp
        equals ((w • v) • ε) • v ^ suc n • w'
            by left right-unit
        equals (w • v) • v ^ suc n • w'
            by assoc
        equals w • v • v ^ suc n • w'
            by right assoc reversed
        equals w • (v • v ^ suc n) • w'
            by definition
        equals w • v ^ suc (suc n) • w'

------------------------------------------------------------------------
-- Basic lemmas about groups

-- We take X and Γ to be fixed throughout the following lemmas, and we
-- assume Γ is group-like.
module Group-Lemmas
       (X : Set)
       (Γ : Context X)
       (group-like : Grouplike Γ)
  where

  open Monoid-Equational

  infix 8 _⁻¹

  -- The inverse of a word.
  _⁻¹ : Word X -> Word X
  [ x ]ʷ ⁻¹ = proj₁ (group-like x)
  ε ⁻¹ = ε
  (u • v) ⁻¹ = v ⁻¹ • u ⁻¹

  -- g ⁻¹ is a left inverse.
  lemma-left-inverse : {g : Word X} -> Γ ⊢ g ⁻¹ • g === ε
  lemma-left-inverse {[ x ]ʷ} = proj₂ (group-like x)
  lemma-left-inverse {ε} = left-unit
  lemma-left-inverse {u • v} =
         equational (v ⁻¹ • u ⁻¹) • (u • v)
                 by assoc
             equals v ⁻¹ • (u ⁻¹ • (u • v))
                 by right assoc reversed
             equals v ⁻¹ • ((u ⁻¹ • u) • v)
                 by right left lemma-left-inverse
             equals v ⁻¹ • ε • v
                 by right left-unit
             equals v ⁻¹ • v
                 by lemma-left-inverse
             equals ε

  -- g ⁻¹ is a right inverse.
  lemma-right-inverse : {g : Word X} -> Γ ⊢ g • g ⁻¹ === ε
  lemma-right-inverse {g} = 
    equational g • (g ⁻¹)
            by left-unit reversed
        equals ε • (g • (g ⁻¹))
            by left lemma-left-inverse reversed
        equals ((g ⁻¹) ⁻¹ • g ⁻¹) • (g • (g ⁻¹))
            by assoc
        equals (g ⁻¹) ⁻¹ • (g ⁻¹ • (g • (g ⁻¹)))
            by right assoc reversed
        equals (g ⁻¹) ⁻¹ • ((g ⁻¹ • g) • g ⁻¹)
            by right left lemma-left-inverse
        equals (g ⁻¹) ⁻¹ • (ε • g ⁻¹)
            by right left-unit
        equals (g ⁻¹) ⁻¹ • g ⁻¹
            by lemma-left-inverse
        equals ε
  
  -- Left cancellation.
  lemma-left-cancel : {g h h' : Word X} -> Γ ⊢ g • h === g • h' -> Γ ⊢ h === h'
  lemma-left-cancel {g} {h} {h'} p = 
    equational h
               by left-unit reversed
        equals ε • h
               by left lemma-left-inverse reversed
        equals (g ⁻¹ • g) • h
               by assoc
        equals g ⁻¹ • (g • h)
               by right p
        equals g ⁻¹ • (g • h')
               by assoc reversed
        equals (g ⁻¹ • g) • h'
               by left lemma-left-inverse
        equals ε • h'
               by left-unit
        equals h'
  
  -- Right cancellation.
  lemma-right-cancel : {g g' h : Word X} -> Γ ⊢ g • h === g' • h -> Γ ⊢ g === g'
  lemma-right-cancel {g} {g'} {h} p = 
    equational g
               by right-unit reversed
        equals g • ε
               by right lemma-right-inverse reversed
        equals g • (h • h ⁻¹)
               by assoc reversed
        equals (g • h) • h ⁻¹
               by left p
        equals (g' • h) • h ⁻¹
               by assoc
        equals g' • (h • h ⁻¹)
               by right lemma-right-inverse
        equals g' • ε
               by right-unit
        equals g'
  
  -- Left inverses are unique.
  lemma-left-inverse-unique : {g h : Word X} -> Γ ⊢ h • g === ε -> Γ ⊢ h === g ⁻¹
  lemma-left-inverse-unique {g} {h} p = 
    equational h
               by right-unit reversed
        equals h • ε
               by right lemma-right-inverse reversed
        equals h • (g • g ⁻¹)
               by assoc reversed
        equals (h • g) • g ⁻¹
               by left p
        equals ε • g ⁻¹
               by left-unit
        equals g ⁻¹
  
  -- Right inverses are unique.
  lemma-right-inverse-unique : {g h : Word X} -> Γ ⊢ g • h === ε -> Γ ⊢ h === g ⁻¹
  lemma-right-inverse-unique {g} {h} p = 
    equational h
               by left-unit reversed
        equals ε • h
               by left lemma-left-inverse reversed
        equals (g ⁻¹ • g) • h
               by assoc
        equals g ⁻¹ • (g • h)
               by right p
        equals g ⁻¹ • ε
               by right-unit
        equals g ⁻¹

  -- Congruence for inverses.
  lemma-cong-inv : {g h : Word X} -> Γ ⊢ g === h -> Γ ⊢ g ⁻¹ === h ⁻¹
  lemma-cong-inv {g} {h} p = lemma-right-inverse-unique claim
     where
       claim : Γ ⊢ h • g ⁻¹ === ε
       claim = equational h • g ⁻¹
                       by left p reversed
                   equals g • g ⁻¹
                       by lemma-right-inverse
                   equals ε

  -- The inverse is involutive.
  lemma-inverse-involutive : {g : Word X} -> Γ ⊢ (g ⁻¹) ⁻¹ === g
  lemma-inverse-involutive {g} = lemma-right-inverse-unique lemma-left-inverse reversed
  
  -- The inverse of ε.
  lemma-unit-inverse : Γ ⊢ ε ⁻¹ === ε
  lemma-unit-inverse = refl
  
  -- The inverse of a product.
  lemma-product-inverse : ∀ {g h : Word X} -> Γ ⊢ (g • h) ⁻¹ === h ⁻¹ • g ⁻¹
  lemma-product-inverse = refl

  -- To show two words are equal, it is sufficient to show their
  -- inverses are equal.
  lemma-rule-inverse : ∀ {u v : Word X} -> Γ ⊢ u ⁻¹ === v ⁻¹ -> Γ ⊢ u === v
  lemma-rule-inverse {u} {v} hyp =
         equational u
                 by right-unit reversed
             equals u • ε
                 by right (lemma-left-inverse reversed)
             equals u • (v ⁻¹ • v)
                 by assoc reversed
             equals (u • v ⁻¹) • v
                 by left (right (hyp reversed))
             equals (u • u ⁻¹) • v
                 by left lemma-right-inverse
             equals ε • v
                 by left-unit
             equals v

  -- Commutativity of inverses. (Note: commutativity is the special
  -- case where v = v' and w = w')
  lemma-comm-inv : ∀ {v v' w w'} -> Γ ⊢ v • w === w' • v' -> Γ ⊢ v' • w ⁻¹ === w' ⁻¹ • v
  lemma-comm-inv {v} {v'} {w} {w'} hyp =
      equational v' • w ⁻¹
              by left-unit reversed
          equals ε • (v' • w ⁻¹)
              by left lemma-left-inverse reversed
          equals (w' ⁻¹ • w') • (v' • w ⁻¹)
              by assoc
          equals w' ⁻¹ • (w' • (v' • w ⁻¹))
              by right assoc reversed
          equals w' ⁻¹ • (w' • v') • w ⁻¹
              by right left hyp reversed
          equals w' ⁻¹ • (v • w) • w ⁻¹
              by right assoc
          equals w' ⁻¹ • v • (w • w ⁻¹)
              by assoc reversed
          equals (w' ⁻¹ • v) • (w • w ⁻¹)
              by right lemma-right-inverse
          equals (w' ⁻¹ • v) • ε
              by right-unit
          equals w' ⁻¹ • v

  -- Any equation can be reduced to a one-sided equation.
  lemma-one-sided : ∀ {w u} -> Γ ⊢ w • u ⁻¹ === ε -> Γ ⊢ w === u
  lemma-one-sided {w} {u} hyp =
      equational w
              by right-unit reversed
          equals w • ε
              by right lemma-left-inverse reversed
          equals w • (u ⁻¹ • u)
              by assoc reversed
          equals (w • u ⁻¹) • u
              by left hyp
          equals ε • u
              by left-unit
          equals u
