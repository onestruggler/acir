------------------------------------------------------------------------
-- Presentations of groups
--
-- This module contains definitions related to semidirect
-- products and normal forms.
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Presentation.Tactics.Equality as Eq using (_≡_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≟_ ; _≤?_)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Word.Base
open import Presentation.Tactics.Judgement
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)

open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words
open import Presentation.Tactics.Lists
open Strict
open InContext
open Associative
open Monoid-Equational
open Monoid-Subtheories

module Examples.Groups.Clifford+CS-3qubit.CosetNF where

-- Definition of monoids that have a normalizing function.
record ListNF {A : Set} (Γ : Context A) : Set where
  field
    listnf : List A -> List A
    lemma-listnf : (xs : List A) -> Γ ⊢ word-of-list xs === word-of-list (listnf xs)

  -- We can use the normalizing function to show equality of monoid
  -- elements.
  listnfeq : {w v : List A} -> listnf w ≡ listnf v -> Γ ⊢ word-of-list w === word-of-list v
  listnfeq {w} {v} hyp =
    equational word-of-list w
           by lemma-listnf w
       equals word-of-list (listnf w)
           by refl' (Eq.cong word-of-list hyp)
       equals word-of-list (listnf v)
           by lemma-listnf v reversed
       equals word-of-list v

  listnfeq' : {w v : Word A} -> listnf (list-of-word w) ≡ listnf (list-of-word v) -> Γ ⊢ w === v
  listnfeq' {w} {v} hyp =
    equational w
           by lemma-list-of-word w
      equals word-of-list (list-of-word w)
           by lemma-listnf (list-of-word w)
       equals word-of-list (listnf (list-of-word w))
           by refl' (Eq.cong word-of-list hyp)
       equals word-of-list (listnf (list-of-word v))
           by lemma-listnf (list-of-word v) reversed
       equals word-of-list (list-of-word v)
           by lemma-list-of-word v reversed
       equals v

-- Expose ListNF. Also, using this special notation makes ListNF an
-- instance record. Such technicalities are used to make the code look
-- nicer.
open ListNF {{...}} public

-- The function extend-nf p nf repeatedly applies nf to the whole list
-- while skipping some part of the list that is indicated by p.
extend-nf : ∀ {A} {Γ : Context A} -> (p : A -> Bool) -> ListNF Γ -> ListNF Γ
extend-nf {A} {Γ} p record { listnf = nf ; lemma-listnf = lemma-nf } = record { listnf = mynf 2000 ; lemma-listnf = lemma-mynf 2000 }
  where
    mynf : ℕ -> List A -> List A
    mynf zero xs = xs
    mynf (suc n) [] = []
    mynf (suc n) (x ∷ xs) with p x
    ... | false = x ∷ mynf n xs
    ... | true with span p (x ∷ xs)
    ... | (l , r) = nf l ++ mynf n r

    lemma-mynf : (n : ℕ) -> (xs : List A) -> Γ ⊢ word-of-list xs === word-of-list (mynf n xs)
    lemma-mynf zero xs = refl
    lemma-mynf (suc n) [] = refl
    lemma-mynf (suc n) (x ∷ xs) with p x
    ... | false = right lemma-mynf n xs
    ... | true with span p (x ∷ xs) | lemma-span p (x ∷ xs)
    ... | (l , r) | pr = d
      where
        d : Γ ⊢ [ x ]ʷ • word-of-list xs === word-of-list (nf l ++ mynf n r)
        d =
          equational [ x ]ʷ • word-of-list xs
            by refl
          equals word-of-list (x ∷ xs)
            by refl' (Eq.cong word-of-list pr)
          equals word-of-list (l ++ r)
            by lemma-append l r reversed
          equals word-of-list l • word-of-list r
            by right lemma-mynf n r
          equals word-of-list l • word-of-list (mynf n r)
            by left lemma-nf l
          equals word-of-list (nf l) • word-of-list (mynf n r)
            by lemma-append (nf l) (mynf n r)
          equals word-of-list (nf l ++ mynf n r)


infixl 4 _∘_

-- Composition of two normalizing functions.
_∘_ : ∀ {A} {Γ : Context A} -> ListNF Γ -> ListNF Γ -> ListNF Γ
_∘_ {A} {Γ} record { listnf = listnf₁ ; lemma-listnf = lemma-listnf₁ } record { listnf = listnf ; lemma-listnf = lemma-listnf } = record { listnf = mynf ; lemma-listnf = lemma-mynf }
  where
    mynf : List A -> List A
    mynf xs = listnf₁ (listnf xs)

    lemma-mynf : (xs : List A) -> Γ ⊢ word-of-list xs === word-of-list (mynf xs)
    lemma-mynf xs = trans (lemma-listnf xs) (lemma-listnf₁ (listnf xs))

rep : ∀ {A} {Γ : Context A} -> ℕ -> ListNF Γ -> ListNF Γ
rep zero nf = nf
rep (suc n) nf = nf ∘ rep n nf


-- Coset normal form.  A version of the coset action that ignores
-- types and operates modulo associativity.
module CosAct {X : Set} {{_ : MaybeEq X}} {Γ : Context X}
  (nfn : ListNF Γ)
  (laction : (g : X) -> (rep : List X) -> 
    Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ word-of-list (g ∷ rep) === word-of-list (rep' ++ g')))
  (raction : (rep : List X) -> (g : X) ->
    Maybe (∃ λ (g' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ g ∷ []) === word-of-list (g' ++ rep')))
    where
    
  lactions : (gs : List X) -> (rep : List X) ->
    Maybe (∃ λ (rep' : List X) -> ∃ λ (gs' : List X) -> Γ ⊢ word-of-list (gs ++ rep) === word-of-list (rep' ++ gs'))
  lactions [] rep rewrite Eq.sym (lemma-append-nil rep) = just (rep , [] , refl' (Eq.cong word-of-list Eq.refl))
  lactions (h ∷ t) rep with lactions t rep
  ... | nothing = nothing
  ... | just (rep' , t' , eq) with laction h rep'
  ... | nothing = nothing
  ... | just (rep'' , h' , eq2) with ListNF.listnf nfn (h' ++ t') | ListNF.lemma-listnf nfn (h' ++ t')
  ... | h'' | eq3 = just (rep'' , h'' , simplify-der 100 d)
    where
      d :  Γ ⊢ word-of-list (h ∷ t ++ rep) === word-of-list (rep'' ++ h'')
      d =
        equational word-of-list (h ∷ t ++ rep)
          by refl
        equals [ h ]ʷ • word-of-list (t ++ rep)
          by right eq
        equals [ h ]ʷ • word-of-list (rep' ++ t')
          by refl
        equals word-of-list (h ∷ rep' ++ t')
          by lemma-append {X = X} {Γ = Γ} (h ∷ rep') t' reversed
        equals word-of-list (h ∷ rep') • word-of-list t'
          by left eq2
        equals word-of-list (rep'' ++ h') • word-of-list t'
          by lemma-append {X = X} {Γ = Γ} (rep'' ++ h') t'
        equals word-of-list ((rep'' ++ h') ++ t')
          by refl' (Eq.cong word-of-list (lemma-append-assoc rep'' h' t'))
        equals word-of-list (rep'' ++ h' ++ t')
          by (lemma-append {X = X} {Γ = Γ} rep'' (h' ++ t')) reversed
        equals word-of-list rep'' • word-of-list (h' ++ t')
          by right eq3
        equals word-of-list rep'' • word-of-list h''
          by lemma-append rep'' h''
        equals word-of-list (rep'' ++ h'')


  ractions : (rep : List X) -> (gs : List X) ->
    Maybe (∃ λ (gs' : List X) -> ∃ λ (rep' : List X) -> Γ ⊢ word-of-list (rep ++ gs) === word-of-list (gs' ++ rep'))
  ractions rep [] rewrite (lemma-append-nil rep) = just ([] , rep , refl)
  ractions rep (h ∷ t) with raction rep h
  ... | nothing = nothing
  ... | just (h' , rep' , eq) with ractions rep' t
  ... | nothing = nothing
  ... | just (t' , rep'' , eq2) with ListNF.listnf nfn (h' ++ t') | ListNF.lemma-listnf nfn (h' ++ t')
  ... | h'' | eq3 = just (h'' , rep'' , simplify-der 100 d)
    where
      d :  Γ ⊢ word-of-list (rep ++ h ∷ t) === word-of-list (h''  ++ rep'')
      d =
        equational word-of-list (rep ++ h ∷ t)
          by refl
        equals word-of-list (rep ++ (h ∷ []) ++ t)
          by refl' (Eq.cong word-of-list (Eq.sym (lemma-append-assoc rep (h ∷ []) t) ))
        equals word-of-list ((rep ++ (h ∷ [])) ++ t)
          by lemma-append {X = X} {Γ = Γ} (rep ++ h ∷ []) t reversed
        equals word-of-list (rep ++ h ∷ []) • word-of-list t
          by left eq
        equals word-of-list (h' ++ rep') • word-of-list t
          by lemma-append (h' ++ rep') t
        equals word-of-list ((h' ++ rep') ++ t)
          by refl' (Eq.cong word-of-list ( (lemma-append-assoc h' rep' t) ))
        equals word-of-list (h' ++ rep' ++ t)
          by lemma-append h' (rep' ++ t) reversed
        equals word-of-list h' • word-of-list (rep' ++ t)
          by right eq2
        equals word-of-list h' • word-of-list (t' ++ rep'')
          by lemma-append h' (t' ++ rep'')
        equals word-of-list (h' ++ t' ++ rep'')
          by refl' (Eq.cong word-of-list (Eq.sym (lemma-append-assoc h' t' rep'') ))
        equals word-of-list ((h' ++ t') ++ rep'')
          by lemma-append (h' ++ t') rep'' reversed
        equals word-of-list (h' ++ t') • word-of-list rep''
          by left eq3
        equals word-of-list (h'') • word-of-list rep''
          by lemma-append h'' rep''
        equals word-of-list (h''  ++ rep'')


  -- Once we have the coset laction (left action) data, we can define
  -- a normalization function on the supergroup.
  lactnf : List X -> List X
  lactnf xs with lactions xs []
  ... | nothing = xs
  ... | just (rep , xs' , eq) = rep ++ xs'

  lemma-lactnf : (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (lactnf xs)
  lemma-lactnf xs with lactions xs []
  ... | nothing = refl
  ... | just (rep , xs' , eq) = simplify-der 100 d
    where
      d : Γ ⊢ word-of-list xs === word-of-list (rep ++ xs')
      d =
        equational word-of-list xs
          by refl' (Eq.cong word-of-list (Eq.sym (lemma-append-nil xs)))
        equals word-of-list (xs ++ [])
          by eq
        equals word-of-list (rep ++ xs')


  -- Similarly, we have right coset normal form.
  ractnf : List X -> List X
  ractnf xs with ractions [] xs
  ... | nothing = xs
  ... | just (xs' , rep , eq) = xs' ++ rep

  lemma-ractnf : (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (ractnf xs)
  lemma-ractnf xs with ractions [] xs
  ... | nothing = refl
  ... | just (xs' , rep , eq) = simplify-der 100 d
    where
      d : Γ ⊢ word-of-list xs === word-of-list (xs' ++ rep)
      d =
        equational word-of-list xs
          by refl' (Eq.cong word-of-list (Eq.sym (lemma-append-nil xs)))
        equals word-of-list (xs ++ [])
          by refl' (Eq.cong word-of-list ((lemma-append-nil xs)))
        equals word-of-list (xs)
          by eq
        equals word-of-list (xs' ++ rep)


  -- The left action normal form when the trivial coset representative
  -- is not literally ε.
  lactnfc : List X -> List X -> List X
  lactnfc c xs with lactions xs c
  ... | nothing = xs
  ... | just (rep , xs' , eq) = rep ++ xs'

  lemma-lactnfc : (c : List X) -> Γ ⊢ word-of-list c === ε -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (lactnfc c xs)
  lemma-lactnfc c p xs with lactions xs c
  ... | nothing = refl
  ... | just (rep , xs' , eq) = simplify-der 100 d
    where
      d : Γ ⊢ word-of-list xs === word-of-list (rep ++ xs')
      d =
        equational word-of-list xs
          by refl' (Eq.cong word-of-list (Eq.sym (lemma-append-nil xs)))
        equals word-of-list (xs ++ [])
          by symm (lemma-append xs [])
        equals word-of-list xs • word-of-list []
          by right symm p
        equals word-of-list xs • word-of-list c
          by lemma-append xs c
        equals word-of-list (xs ++ c)
          by eq
        equals word-of-list (rep ++ xs')


  lactnfeq : {w v : List X} -> lactnf w ≡ lactnf v -> Γ ⊢ word-of-list w === word-of-list v
  lactnfeq {w} {v} hyp =
    equational word-of-list w
           by lemma-lactnf w
       equals word-of-list (lactnf w)
           by refl' (Eq.cong word-of-list hyp)
       equals word-of-list (lactnf v)
           by lemma-lactnf v reversed
       equals word-of-list v


  -- For reusing the rewrite-in-context' tactic.
  multistep : ℕ -> List X -> List X
  multistep n = lactnf

  lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)
  lemma-multistep n = lemma-lactnf

  rewrite-tactic : ∀ {s t pre post s2 t2} -> (n m m' k : ℕ) ->
             let s' = list-of-word2 s
                 t' = list-of-word2 t
             in (mysplit n m s' , mysplit n m' t' , multistep k (list-of-word s2)) ≡ 
                ((pre , s2 , post) , (pre , t2 , post) , (list-of-word t2)) ->
                Γ ⊢ s === t
  rewrite-tactic = rewrite-in-context' multistep lemma-multistep

-- A version of SemiDirect that ignores types and operates modulo
-- associativity.
module SemiDirect {X : Set} {{_ : MaybeEq X}} {Γ : Context X}
  (isH : X -> Bool)
  (isN : X -> Bool)
  (nfh : ListNF Γ)
  (nfn : ListNF Γ)
  (group-like : Grouplike Γ)
  (conj : (h n : X) -> Maybe (∃ λ (n' : List X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === word-of-list n' • [ h ]ʷ))
    where

  conj1s : (h : X) -> (n : List X) -> Maybe (∃ λ (n' : List X) -> Γ ⊢ [ h ]ʷ • word-of-list n === word-of-list n' •  [ h ]ʷ)
  conj1s h [] = just ([] , trans right-unit (symm left-unit))
  conj1s h ns@(n ∷ ns') with conj h n | conj1s h ns'
  ... | just x | nothing = nothing
  ... | nothing | just x = nothing
  ... | nothing | nothing = nothing
  ... | just (n' , prh) | just (ns'' , prt) = just (n' ++ ns'' , simplify-der 100 d)
    where
      d : Γ ⊢ [ h ]ʷ • word-of-list ns === word-of-list (n' ++ ns'') • [ h ]ʷ
      d =
        equational [ h ]ʷ • word-of-list ns
          by refl
        equals [ h ]ʷ • [ n ]ʷ • word-of-list ns'
          by symm assoc
        equals ([ h ]ʷ • [ n ]ʷ) • word-of-list ns'
          by left prh
        equals (word-of-list n' • [ h ]ʷ) • word-of-list ns'
          by assoc
        equals word-of-list n' • [ h ]ʷ • word-of-list ns'
          by right prt
        equals word-of-list n' • word-of-list ns'' • [ h ]ʷ
          by symm assoc
        equals (word-of-list n' • word-of-list ns'') • [ h ]ʷ
          by left lemma-append n' ns''
        equals word-of-list (n' ++ ns'') • [ h ]ʷ
        
  conjs : (h : List X) -> (n : List X) -> Maybe (∃ λ (n' : List X) -> Γ ⊢ word-of-list (h ++ n) === word-of-list (n' ++ h))
  conjs [] n rewrite (Eq.sym (lemma-append-nil n)) = just (n , refl)
  conjs hs@(h ∷ hs') n with conjs hs' n
  ... | nothing = nothing
  ... | just (n' , pr') with conj1s h n'
  ... | nothing = nothing
  ... | just (n'' , pr'') = just (n'' , simplify-der 100 d)
    where
      d : Γ ⊢ word-of-list (hs ++ n) === word-of-list (n'' ++ hs)
      d =
        equational word-of-list (hs ++ n)
          by refl
        equals word-of-list (h ∷ (hs' ++ n))
          by refl
        equals [ h ]ʷ • word-of-list (hs' ++ n)
          by right pr'
        equals [ h ]ʷ • word-of-list (n' ++ hs')
          by refl
        equals word-of-list (h ∷ (n' ++ hs'))
          by refl
        equals word-of-list ((h ∷ n') ++ hs')
          by (lemma-append {Γ = Γ} (h ∷ n') hs') reversed
        equals word-of-list (h ∷ n') • word-of-list hs'
          by left pr''
        equals (word-of-list n'' • [ h ]ʷ) • word-of-list hs'
          by assoc
        equals word-of-list n'' • [ h ]ʷ • word-of-list hs'
          by refl
        equals word-of-list n'' • word-of-list (h ∷ hs')
          by lemma-append n'' (h ∷ hs')
        equals word-of-list (n'' ++ hs)

  aux2 : (n : List X) -> (h : List X) -> (w : List X) -> Maybe (∃ λ (n' : List X) -> (∃ λ (h' : List X) -> Γ ⊢ word-of-list (n ++ h ++ w) === word-of-list (n' ++ h')))
  aux2 n h [] rewrite (lemma-append-nil h)= just ( n , h , refl)
  aux2 n h ws@(w ∷ ws') with isH w | isN w 
  aux2 n h (w ∷ ws') | false | false = nothing
  aux2 n h (w ∷ ws') | true | true = nothing
  aux2 n h (w ∷ ws') | true | false with aux2 n (h ++ w ∷ []) ws'
  aux2 n h (w ∷ ws') | true | false | nothing = nothing
  aux2 n h (w ∷ ws') | true | false | just (n' , h' , pr) rewrite (lemma-append-assoc h (w ∷ []) ws') = just (n' , h' , pr)
  aux2 n h (w ∷ ws') | false | true with conjs h (w ∷ [])
  aux2 n h (w ∷ ws') | false | true | nothing = nothing
  aux2 n h (w ∷ ws') | false | true | just (w' , pr2) with aux2 (n ++ w') h ws'
  aux2 n h (w ∷ ws') | false | true | just (w' , pr2) | nothing = nothing
  aux2 n h (w ∷ ws') | false | true | just (w' , pr2) | just (n' , h' , pr3) = just (n' , h' , simplify-der 100 d)
    where
      d : Γ ⊢ word-of-list (n ++ h ++ w ∷ ws') === word-of-list (n' ++ h')
      d =
        equational word-of-list (n ++ h ++ w ∷ ws')
          by refl' (Eq.cong word-of-list (Eq.cong (n ++_) (lemma-append-∷ h w ws')))
        equals word-of-list (n ++ (h ++ w ∷ []) ++ ws')
          by lemma-append n ((h ++ w ∷ []) ++ ws') reversed
        equals word-of-list n • word-of-list ((h ++ w ∷ []) ++ ws')
          by right lemma-append (h ++ w ∷ []) ws' reversed
        equals word-of-list n • word-of-list (h ++ w ∷ []) • word-of-list ws'
          by right left pr2
        equals word-of-list n • word-of-list (w' ++ h) • word-of-list ws'
          by right left (lemma-append w' h) reversed
        equals word-of-list n • (word-of-list w' • word-of-list h) • word-of-list ws'
          by right assoc
        equals word-of-list n • word-of-list w' • word-of-list h • word-of-list ws'
          by right right lemma-append h ws'
        equals word-of-list n • word-of-list w' • word-of-list (h ++ ws')
          by symm assoc
        equals (word-of-list n • word-of-list w') • word-of-list (h ++ ws')
          by left lemma-append n w'
        equals word-of-list (n ++ w') • word-of-list (h ++ ws')
          by lemma-append (n ++ w') (h ++ ws')
        equals word-of-list ((n ++ w') ++ (h ++ ws'))
          by pr3
        equals word-of-list (n' ++ h')

  nfnh : (w : List X) -> Maybe (∃ λ (w' : List X) -> Γ ⊢ word-of-list w === word-of-list w')
  nfnh w with aux2 [] [] w
  ... | nothing = nothing
  ... | just (n , h , pr) with ListNF.listnf nfh h | ListNF.lemma-listnf nfh h | ListNF.listnf nfn n | ListNF.lemma-listnf nfn n
  ... | h' | pr4 | n' | pr3 = just (n' ++ h' , simplify-der 100 d)
    where
      d : Γ ⊢ word-of-list w === word-of-list (n' ++  h')
      d =
        equational word-of-list w
          by pr
        equals word-of-list (n ++ h)
          by lemma-append n h reversed
        equals word-of-list n • word-of-list h
          by cong pr3 pr4
        equals word-of-list n' • word-of-list h'
          by lemma-append n' h'
        equals word-of-list (n' ++  h')


  nfnh' : List X -> List X
  nfnh' w with nfnh w
  ... | nothing = w
  ... | just (w' , pr) = w'

  lemma-nfnh' : (w : List X) -> Γ ⊢ word-of-list w === word-of-list (nfnh' w)
  lemma-nfnh' w with nfnh w
  ... | nothing = refl
  ... | just (w' , pr) = pr

  nfeq : {w v : List X} -> nfnh' w ≡ nfnh' v -> Γ ⊢ word-of-list w === word-of-list v
  nfeq {w} {v} hyp =
    equational word-of-list w
           by lemma-nfnh' w
       equals word-of-list (nfnh' w)
           by refl' (Eq.cong word-of-list hyp)
       equals word-of-list (nfnh' v)
           by lemma-nfnh' v reversed
       equals word-of-list v


  multistep-nh : ℕ -> List X -> List X
  multistep-nh n = nfnh'

  lemma-multistep-nh : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep-nh n xs)
  lemma-multistep-nh n = lemma-nfnh'

  nh-rewrite-tactic : ∀ {s t pre post s2 t2} -> (n m m' k : ℕ) ->
             let s' = list-of-word2 s
                 t' = list-of-word2 t
             in (mysplit n m s' , mysplit n m' t' , multistep-nh k (list-of-word s2)) ≡ 
                ((pre , s2 , post) , (pre , t2 , post) , (list-of-word t2)) ->
                Γ ⊢ s === t
  nh-rewrite-tactic = rewrite-in-context' multistep-nh lemma-multistep-nh

-- Step3 depends on this module. We first defined NF, Coset, and
-- SemiDirect using Word instead of List, but later we switched to
-- List. Some files still depend on the old definition.
module Legacy where 

  listf-of-f : ∀ {A} (f : Word A -> Word A) -> List A -> List A
  listf-of-f {A} f xs = list-of-word (f (word-of-list xs))

  lemma-listf-of-f : ∀ {A} {Γ : Context A} {f : Word A -> Word A} -> (pf : ∀ (w : Word A) -> Γ ⊢ w === f w) -> (xs : List A) -> Γ ⊢ word-of-list xs === word-of-list (listf-of-f f xs)
  lemma-listf-of-f {f = f} pf xs =
    equational word-of-list xs
      by pf (word-of-list xs)
    equals (f (word-of-list xs))
      by lemma-list-of-word (f (word-of-list xs))
    equals word-of-list (list-of-word (f (word-of-list xs)))
      by refl' (Eq.cong word-of-list Eq.refl) reversed
    equals word-of-list (listf-of-f f xs)


  f-of-listf : ∀ {A} (f : List A -> List A) -> Word A -> Word A
  f-of-listf {A} f xs = word-of-list (f (list-of-word xs))

  lemma-f-of-listf : ∀ {A} {Γ : Context A} {f : List A -> List A} -> (pf : ∀ (w : List A) -> Γ ⊢ word-of-list w === word-of-list (f w)) -> (xs : Word A) -> Γ ⊢ xs === (f-of-listf f xs)
  lemma-f-of-listf {f = f} pf xs =
    equational xs
      by lemma-list-of-word xs
    equals word-of-list (list-of-word xs)
      by pf (list-of-word xs)
    equals (word-of-list (f (list-of-word xs)))
      by refl
    equals (f-of-listf f xs)



  record NF {A : Set} (Γ : Context A) : Set where
    field
      nf : Word A -> Word A
      lemma-nf : (xs : Word A) -> Γ ⊢ xs === nf xs
    nfeq : {w v : Word A} -> nf w ≡ nf v -> Γ ⊢ w === v
    nfeq {w} {v} hyp =
      equational w
             by lemma-nf w
         equals nf w
             by refl' hyp
         equals nf v
             by lemma-nf v reversed
         equals v

  record LRNF {A : Set} (Γ : Context A) : Set where
    field
      lnf : Word A -> Word A
      lemma-lnf : (xs : Word A) -> Γ ⊢ xs === lnf xs
      rnf : Word A -> Word A
      lemma-rnf : (xs : Word A) -> Γ ⊢ xs === rnf xs


  -- A version of the coset action that ignores types.
  module CosAct' {X : Set} {{_ : MaybeEq X}} {Γ : Context X}
    (nfn : NF Γ)
    (laction : (g : X) -> (rep : Word X) -> 
      Maybe (∃ λ (rep' : Word X) -> ∃ λ (g' : Word X) -> Γ ⊢ [ g ]ʷ • rep === rep' • g'))
    (raction : (rep : Word X) -> (g : X) ->
      Maybe (∃ λ (g' : Word X) -> ∃ λ (rep' : Word X) -> Γ ⊢ rep • [ g ]ʷ === g' • rep'))
      where


    lactions : (gs : Word X) -> (rep : Word X) ->
      Maybe (∃ λ (rep' : Word X) -> ∃ λ (gs' : Word X) -> Γ ⊢ gs • rep === rep' • gs')
    lactions ([ x ]ʷ) rep = laction x rep
    lactions ε rep = just (rep , ε , trans left-unit (symm right-unit))
    lactions (gs • gs₁) rep with lactions gs₁ rep
    ... | nothing = nothing
    ... | just (rep' , gs₁' , eq) with lactions gs rep'
    ... | nothing = nothing
    ... | just (rep'' , gs' , eq2) with NF.nf nfn (gs' • gs₁') | NF.lemma-nf nfn (gs' • gs₁')
    ... | gs'' | eq3 = just (rep'' , gs'' , simplify-der 100 d1)
      where
        d1 :  Γ ⊢ (gs • gs₁) • rep === rep'' • gs''
        d1 =
          equational (gs • gs₁) • rep
            by assoc
          equals gs • (gs₁ • rep)
            by (right eq)
          equals gs • (rep' • gs₁')
            by symm assoc
          equals (gs • rep') • gs₁'
            by (left eq2)
          equals (rep'' • gs') • gs₁'
            by assoc
          equals rep'' • gs' • gs₁'
            by (right eq3)
          equals rep'' • gs''


    -- Once we have the coset laction (left action) data, we can
    -- define a normalization function on the supergroup.
    lactnf : Word X -> Word X
    lactnf xs with lactions xs ε
    ... | nothing = xs
    ... | just (rep , xs' , eq) with NF.nf nfn xs'
    ... | xs'' = rep • xs''

    lemma-lactnf : (xs : Word X) -> Γ ⊢ xs === lactnf xs
    lemma-lactnf xs with lactions xs ε
    ... | nothing = refl
    ... | just (rep , xs' , eq) with NF.lemma-nf nfn xs'
    ... | pr = simplify-der 100 (trans (trans (symm right-unit) eq) (cong refl pr))

    lactnfeq : {w v : Word X} -> lactnf w ≡ lactnf v -> Γ ⊢ w === v
    lactnfeq {w} {v} hyp =
      equational w
             by lemma-lactnf w
         equals lactnf w
             by refl' hyp
         equals lactnf v
             by lemma-lactnf v reversed
         equals v


    ractions : (rep : Word X) -> (gs : Word X) ->
      Maybe (∃ λ (gs' : Word X) -> ∃ λ (rep' : Word X) -> Γ ⊢ rep • gs === gs' • rep')
    ractions rep ([ x ]ʷ) = raction rep x
    ractions rep ε = just (ε , rep , trans right-unit (symm left-unit))
    ractions rep (gs • gs₁) with ractions rep gs
    ... | nothing = nothing
    ... | just (gs' , rep' , eq) with ractions rep' gs₁
    ... | nothing = nothing
    ... | just (gs₁' , rep'' , eq2) with NF.nf nfn (gs' • gs₁') | NF.lemma-nf nfn (gs' • gs₁')
    ... | gs'' | eq3 = just (gs'' , rep'' , simplify-der 100 d1)
      where
        d1 :  Γ ⊢ rep • (gs • gs₁) === gs'' • rep''
        d1 =
          equational rep • (gs • gs₁)
            by symm assoc
          equals (rep • gs) • gs₁
            by (left eq)
          equals (gs' • rep') • gs₁
            by assoc
          equals gs' • rep' • gs₁
            by (right eq2)
          equals gs' • gs₁' • rep''
            by symm assoc
          equals (gs' • gs₁') • rep''
            by (left eq3)
          equals gs'' • rep''


    -- Once we have the coset raction (right action) data, we can
    -- define a normalization function on the supergroup.
    ractnf : Word X -> Word X
    ractnf xs with ractions ε xs
    ... | nothing = xs
    ... | just (xs' , rep , eq) with NF.nf nfn xs'
    ... | xs'' = xs'' • rep

    lemma-ractnf : (xs : Word X) -> Γ ⊢ xs === ractnf xs
    lemma-ractnf xs with ractions ε xs
    ... | nothing = refl
    ... | just (xs' , rep , eq) with NF.lemma-nf nfn xs'
    ... | pr = simplify-der 100 (trans (trans (symm left-unit) eq) (cong pr refl))


    ractnfeq : {w v : Word X} -> ractnf w ≡ ractnf v -> Γ ⊢ w === v
    ractnfeq {w} {v} hyp =
      equational w
             by lemma-ractnf w
         equals ractnf w
             by refl' hyp
         equals ractnf v
             by lemma-ractnf v reversed
         equals v

    multistep : ℕ -> List X -> List X
    multistep n = listf-of-f lactnf

    lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)
    lemma-multistep n = lemma-listf-of-f lemma-lactnf

    rewrite-tactic : ∀ {s t pre post s2 t2} -> (n m m' k : ℕ) ->
               let s' = list-of-word2 s
                   t' = list-of-word2 t
               in (mysplit n m s' , mysplit n m' t' , multistep k (list-of-word s2)) ≡ 
                  ((pre , s2 , post) , (pre , t2 , post) , (list-of-word t2)) ->
                  Γ ⊢ s === t
    rewrite-tactic = rewrite-in-context' multistep lemma-multistep

  -- A version of SemiDirect that ignores types.
  module SemiDirect' {X : Set} {{_ : MaybeEq X}} {Γ : Context X}
    (isH : X -> Bool)
    (isN : X -> Bool)
    (nfh : NF Γ)
    (nfn : NF Γ)
    (group-like : Grouplike Γ)
    (conj : (h n : X) -> Maybe (∃ λ (n' : Word X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === n' • [ h ]ʷ))
      where

    conj1s : (h : X) -> (n : Word X) -> Maybe (∃ λ (n' : Word X) -> Γ ⊢ [ h ]ʷ • n === n' •  [ h ]ʷ)
    conj1s h ([ x ]ʷ) = conj h x
    conj1s h ε = just (ε , trans right-unit (symm left-unit))
    conj1s h n@(n₁ • n₂) with conj1s h n₁ | conj1s h n₂
    ... | just x | nothing = nothing
    ... | nothing | just x = nothing
    ... | nothing | nothing = nothing
    ... | just (n₁' , pr₁) | just (n₂' , pr₂) with NF.nf nfn (n₁' • n₂') | NF.lemma-nf nfn (n₁' • n₂')
    ... | n'' | pr'' = just (n'' , d)
      where
        d : Γ ⊢ [ h ]ʷ • n === n'' • [ h ]ʷ
        d =
          equational [ h ]ʷ • n
            by refl
          equals [ h ]ʷ •  (n₁ • n₂)
            by refl
          equals [ h ]ʷ •  (n₁ • n₂)
            by symm assoc
          equals ([ h ]ʷ •  n₁) • n₂
            by left pr₁
          equals (n₁' • [ h ]ʷ) • n₂
            by assoc
          equals n₁' • ([ h ]ʷ • n₂)
            by right pr₂
          equals n₁' • (n₂' • [ h ]ʷ)
            by symm assoc
          equals (n₁' • n₂') • [ h ]ʷ
            by left pr''
          equals n'' • [ h ]ʷ

    conjs : (h : Word X) -> (n : Word X) -> Maybe (∃ λ (n' : Word X) -> Γ ⊢ h • n === n' • h)
    conjs ([ x ]ʷ) n = conj1s x n
    conjs ε n = just (n , (trans left-unit (symm right-unit)))
    conjs h@(h₁ • h₂) n with conjs h₂ n
    ... | nothing = nothing
    ... | just (n' , pr') with conjs h₁ n'
    ... | nothing = nothing
    ... | just (n'' , pr'') = just (n'' , d)
      where
        d : Γ ⊢ h • n === n'' •  h
        d =
          equational h • n
            by assoc
          equals h₁ • h₂ • n
            by right pr'
          equals h₁ • n' • h₂
            by symm assoc
          equals (h₁ • n') • h₂
            by left pr''
          equals (n'' • h₁) • h₂
            by assoc
          equals n'' •  h

    open Group-Lemmas X Γ group-like

    conjs' : (n : Word X) -> (h : Word X) -> Maybe (∃ λ (n' : Word X) -> Γ ⊢ n • h === h • n')
    conjs' n h with conjs (h ⁻¹) (n)
    ... | nothing = nothing
    ... | just (m , pr) = just (m , d)
      where
        d : Γ ⊢ n • h === h • m
        d =
          equational n • h
            by symm left-unit
          equals ε • n • h
            by left symm lemma-right-inverse
          equals (h • (h ⁻¹)) • n • h
            by trans assoc (right symm assoc)
          equals h • ((h ⁻¹) • n) • h
            by right left pr
          equals h • (m • (h ⁻¹)) • h
            by right assoc
          equals h • m • (h ⁻¹) • h
            by right right lemma-left-inverse
          equals h • m • ε
            by symm assoc
          equals (h • m) • ε
            by right-unit
          equals h • m



    aux : (h : Word X) -> (n : Word X) -> (w : Word X) -> Maybe (∃ λ (h' : Word X) -> (∃ λ (n' : Word X) -> Γ ⊢ h • n • w === h' • n'))
    aux h n ε = just ( h , n , cong refl right-unit)
    aux h n ([ x ]ʷ) with isH x | isN x
    ... | true | true = nothing
    ... | false | false  = nothing
    ... | false | true = just (h ,  n • [ x ]ʷ , refl)
    ... | true | false with conjs' n ([ x ]ʷ)
    ... | nothing = nothing
    ... | just (m' , pr1) = just (h • [ x ]ʷ , m' , d)
      where
        d :  Γ ⊢ h • n • ([ x ]ʷ) === (h • [ x ]ʷ) • m'
        d =
          equational h • n • [ x ]ʷ
            by right pr1
          equals h • [ x ]ʷ • m'
            by symm assoc
          equals (h • [ x ]ʷ) • m'
    aux h n (w • w₁) with aux h n w
    ... | nothing = nothing
    ... | just (h' , n' , pr') with aux h' n' w₁
    ... | nothing = nothing
    ... | just (h'' , n'' , pr'') = just(h'' , n'' , d)
      where
        d : Γ ⊢ h • n • (w • w₁) === h'' • n''
        d =
          equational h • n • (w • w₁)
            by right symm assoc
          equals h • (n • w) • w₁
            by symm assoc
          equals (h • (n • w)) • w₁
            by left pr'
          equals (h' • n') • w₁
            by assoc
          equals h' • (n' • w₁)
            by pr''
          equals h'' • n''


    nfhn : (w : Word X) -> Maybe (∃ λ (w' : Word X) -> Γ ⊢ w === w')
    nfhn w with aux ε ε w
    ... | nothing = nothing
    ... | just (h , n , pr) with NF.nf nfh h | NF.lemma-nf nfh h | NF.nf nfn n | NF.lemma-nf nfn n
    ... | h' | pr1 | n' | pr2 = just (h' • n' , simplify-der 100 d)
      where
        d1 :  Γ ⊢ h • n === h' • n'
        d1 = cong pr1 pr2
        d : Γ ⊢ w === h' • n'
        d = trans (trans (symm left-unit) (trans (symm left-unit) pr) ) d1


    aux2 : (n : Word X) -> (h : Word X) -> (w : Word X) -> Maybe (∃ λ (n' : Word X) -> (∃ λ (h' : Word X) -> Γ ⊢ n • h • w === n' • h'))
    aux2 n h ε = just ( n , h , cong refl right-unit)
    aux2 n h ([ x ]ʷ) with isN x | isH x
    ... | true | true = nothing
    ... | false | false  = nothing
    ... | false | true = just (n ,  h • [ x ]ʷ , refl)
    ... | true | false with conjs h ([ x ]ʷ)
    ... | nothing = nothing
    ... | just (m' , pr1) = just (n • m' , h , d)
      where
        d :  Γ ⊢ n • h • ([ x ]ʷ) === (n • m') • h
        d =
          equational n • h • [ x ]ʷ
            by right pr1
          equals n • m' • h
            by symm assoc
          equals (n • m') • h
    aux2 n h (w • w₁) with aux2 n h w
    ... | nothing = nothing
    ... | just (n' , h' , pr') with aux2 n' h' w₁
    ... | nothing = nothing
    ... | just (n'' , h'' , pr'') = just(n'' , h'' , d)
      where
        d : Γ ⊢ n • h • (w • w₁) === n'' • h''
        d =
          equational n • h • (w • w₁)
            by right symm assoc
          equals n • (h • w) • w₁
            by symm assoc
          equals (n • (h • w)) • w₁
            by left pr'
          equals (n' • h') • w₁
            by assoc
          equals n' • (h' • w₁)
            by pr''
          equals n'' • h''


    nfnh : (w : Word X) -> Maybe (∃ λ (w' : Word X) -> Γ ⊢ w === w')
    nfnh w with aux2 ε ε w 
    ... | nothing = nothing
    ... | just (n , h , pr) with NF.nf nfh h | NF.lemma-nf nfh h | NF.nf nfn n | NF.lemma-nf nfn n
    ... | h' | pr4 | n' | pr3 = just (n' • h' , simplify-der 100 d)
      where
        d : Γ ⊢ w === n' • h'
        d =
          equational w
            by symm (trans left-unit left-unit)
          equals ε • ε • w
            by pr
          equals n • h
            by cong pr3 pr4
          equals n' • h'


    nfhn' : Word X -> Word X
    nfhn' w with nfhn w
    ... | nothing = w
    ... | just (w' , pr) = w'

    lemma-nfhn' : (w : Word X) -> Γ ⊢ w === nfhn' w
    lemma-nfhn' w with nfhn w
    ... | nothing = refl
    ... | just (w' , pr) = pr


    multistep : ℕ -> List X -> List X
    multistep n = listf-of-f nfhn'

    lemma-multistep : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep n xs)
    lemma-multistep n = lemma-listf-of-f lemma-nfhn'

    rewrite-tactic : ∀ {s t pre post s2 t2} -> (n m m' k : ℕ) ->
               let s' = list-of-word2 s
                   t' = list-of-word2 t
               in (mysplit n m s' , mysplit n m' t' , multistep k (list-of-word s2)) ≡ 
                  ((pre , s2 , post) , (pre , t2 , post) , (list-of-word t2)) ->
                  Γ ⊢ s === t
    rewrite-tactic = rewrite-in-context' multistep lemma-multistep


    nfnh' : Word X -> Word X
    nfnh' w with nfnh w
    ... | nothing = w
    ... | just (w' , pr) = w'

    lemma-nfnh' : (w : Word X) -> Γ ⊢ w === nfnh' w
    lemma-nfnh' w with nfnh w
    ... | nothing = refl
    ... | just (w' , pr) = pr

    nfeq : {w v : Word X} -> nfhn' w ≡ nfhn' v -> Γ ⊢ w === v
    nfeq {w} {v} hyp =
      equational w
             by lemma-nfhn' w
         equals nfhn' w
             by refl' hyp
         equals nfhn' v
             by lemma-nfhn' v reversed
         equals v


    multistep-nh : ℕ -> List X -> List X
    multistep-nh n = listf-of-f nfnh'

    lemma-multistep-nh : (n : ℕ) -> (xs : List X) -> Γ ⊢ word-of-list xs === word-of-list (multistep-nh n xs)
    lemma-multistep-nh n = lemma-listf-of-f lemma-nfnh'

    nh-rewrite-tactic : ∀ {s t pre post s2 t2} -> (n m m' k : ℕ) ->
               let s' = list-of-word2 s
                   t' = list-of-word2 t
               in (mysplit n m s' , mysplit n m' t' , multistep-nh k (list-of-word s2)) ≡ 
                  ((pre , s2 , post) , (pre , t2 , post) , (list-of-word t2)) ->
                  Γ ⊢ s === t
    nh-rewrite-tactic = rewrite-in-context' multistep-nh lemma-multistep-nh

