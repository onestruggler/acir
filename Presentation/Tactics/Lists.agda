------------------------------------------------------------------------
-- Presentations of groups
--
-- Operations on lists used by the tactics of Presentation.Tactics
-- (from the list library of the Bian–Selinger Agda code, CC BY 2.0),
-- on the lists of the standard library: membership, splitting,
-- reversal, spans, list quantification, strict application, lists over
-- a sum of alphabets, finiteness and proofs by finite case analysis;
-- and semi-decidable equality (MaybeEq).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Presentation.Tactics.Lists where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base public using (List ; [] ; _∷_ ; map ; length ; _++_ ; concat)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Presentation.Tactics.Judgement using (_∪_ ; ⌜_ ; _⌝)

------------------------------------------------------------------------
-- Membership

data mem {X : Set} (x : X) : List X → Set where
  mem-head : ∀ {xs} → mem x (x ∷ xs)
  mem-tail : ∀ {y xs} → mem x xs → mem x (y ∷ xs)

nth : {X : Set} → ℕ → List X → Maybe X
nth n [] = nothing
nth zero (x ∷ xs) = just x
nth (suc n) (x ∷ xs) = nth n xs

lemma-mem-nth : ∀ {X : Set} {x : X} {xs : List X} (n : ℕ) → nth n xs ≡ just x → mem x xs
lemma-mem-nth {xs = []} n ()
lemma-mem-nth {xs = x ∷ xs} zero refl = mem-head
lemma-mem-nth {xs = x ∷ xs} (suc n) hyp = mem-tail (lemma-mem-nth n hyp)

lemma-mem-map : {X Y : Set} → (f : X → Y) → (xs : List X) → ∀ x → mem x xs → mem (f x) (map f xs)
lemma-mem-map f [] x ()
lemma-mem-map f (x ∷ xs) .x mem-head = mem-head
lemma-mem-map f (x ∷ xs) y (mem-tail hyp) = mem-tail (lemma-mem-map f xs y hyp)

lemma-mem-append1 : ∀ {X} → (xs ys : List X) → {x : X} → mem x xs → mem x (xs ++ ys)
lemma-mem-append1 [] ys ()
lemma-mem-append1 (x ∷ xs) ys mem-head = mem-head
lemma-mem-append1 (a ∷ xs) ys (mem-tail hyp) = mem-tail (lemma-mem-append1 xs ys hyp)

lemma-mem-append2 : ∀ {X} → (xs ys : List X) → {x : X} → mem x ys → mem x (xs ++ ys)
lemma-mem-append2 [] ys hyp = hyp
lemma-mem-append2 (x ∷ xs) ys hyp = mem-tail (lemma-mem-append2 xs ys hyp)

lemma-mem-concat : ∀ {X} → (xss : List (List X)) → ∀ {x} {xs} → mem x xs → mem xs xss → mem x (concat xss)
lemma-mem-concat [] mem-x ()
lemma-mem-concat (xs ∷ xss) mem-x mem-head = lemma-mem-append1 xs (concat xss) mem-x
lemma-mem-concat (y ∷ xss) mem-x (mem-tail mem-xs) = lemma-mem-append2 y (concat xss) (lemma-mem-concat xss mem-x mem-xs)

------------------------------------------------------------------------
-- Reversal

-- Append the second list to the reverse of the first.
reverse-append : ∀ {X : Set} → List X → List X → List X
reverse-append [] ys = ys
reverse-append (x ∷ xs) ys = reverse-append xs (x ∷ ys)

reverse : ∀ {X : Set} → List X → List X
reverse xs = reverse-append xs []

------------------------------------------------------------------------
-- Splitting

-- A prefix of length up to n, and the remainder.
split : ∀ {X : Set} → ℕ → List X → List X × List X
split n [] = ([] , [])
split zero (x ∷ xs) = ([] , x ∷ xs)
split (suc n) (x ∷ xs) with split n xs
... | (xs1 , xs2) = (x ∷ xs1 , xs2)

lemma-split : ∀ {X : Set} → (n : ℕ) → (xs : List X) → ∀ {ys zs} → split n xs ≡ (ys , zs) → ys ++ zs ≡ xs
lemma-split n [] refl = refl
lemma-split zero (x ∷ xs) refl = refl
lemma-split (suc n) (x ∷ xs) eq with split n xs | lemma-split n xs
lemma-split (suc n) (x ∷ xs) refl | (xs1 , xs2) | ih = Eq.cong (x ∷_) (ih refl)

-- Three parts (x , y , z), x of length up to n, y up to m.
split3 : ∀ {X : Set} → ℕ → ℕ → List X → List X × List X × List X
split3 n m xs with split n xs
... | (x , ys) with split m ys
... | (y , z) = (x , y , z)

lemma-split3 : ∀ {X : Set} → (n m : ℕ) → (xs : List X) → ∀ {x y z} → split3 n m xs ≡ (x , y , z) → x ++ y ++ z ≡ xs
lemma-split3 n m xs hyp with split n xs in eq1
lemma-split3 n m xs hyp | (x , ys) with split m ys in eq2
lemma-split3 n m xs refl | x , ys | y , z =
  Eq.trans (Eq.cong (x ++_) (lemma-split m ys eq2)) (lemma-split n xs eq1)

-- Span a list by a predicate.
span : ∀ {A : Set} → (p : A → Bool) → List A → List A × List A
span p [] = [] , []
span p (x ∷ xs) with p x
... | false = [] , x ∷ xs
... | true with span p xs
... | (l , r) = x ∷ l , r

lemma-span : ∀ {A : Set} → (p : A → Bool) → (xs : List A) → let sp = span p xs in xs ≡ proj₁ sp ++ proj₂ sp
lemma-span p [] = refl
lemma-span p (x ∷ xs) with p x
... | false = refl
... | true with span p xs | lemma-span p xs
... | x₁ , x₂ | ihp rewrite ihp = refl

------------------------------------------------------------------------
-- Products and appending

list-prod : ∀ {X Y : Set} → List X → List Y → List (X × Y)
list-prod xs ys = concat (map (λ y → map (λ x → (x , y)) xs) ys)

lemma-mem-list-prod : ∀ {X Y : Set} → (xs : List X) → (ys : List Y) → ∀ {x y} → mem x xs → mem y ys → mem (x , y) (list-prod xs ys)
lemma-mem-list-prod xs ys {x} {y} p q =
  let p' : mem (x , y) (map (λ x → (x , y)) xs)
      p' = lemma-mem-map (λ x → (x , y)) xs x p

      q' : mem (map (λ x → (x , y)) xs) (map (λ y → map (λ x → (x , y)) xs) ys)
      q' = lemma-mem-map (λ y → map (λ x → x , y) xs) ys y q
  in
    lemma-mem-concat (map (λ y → map (λ x → x , y) xs) ys) p' q'

lemma-append-nil : ∀ {X : Set} (xs : List X) → xs ++ [] ≡ xs
lemma-append-nil [] = refl
lemma-append-nil (x ∷ xs) = Eq.cong (x ∷_) (lemma-append-nil xs)

lemma-append-assoc : ∀ {X : Set} (xs ys zs : List X) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
lemma-append-assoc [] ys zs = refl
lemma-append-assoc (x ∷ xs) ys zs = Eq.cong (x ∷_) (lemma-append-assoc xs ys zs)

lemma-∷-append : ∀ {X : Set} (x : X) (xs ys : List X) → x ∷ xs ++ ys ≡ x ∷ (xs ++ ys)
lemma-∷-append x xs ys = refl

lemma-append-∷ : ∀ {X : Set} (xs : List X) (y : X) (ys : List X) → xs ++ y ∷ ys ≡ (xs ++ y ∷ []) ++ ys
lemma-append-∷ [] y ys = refl
lemma-append-∷ (x ∷ xs) y ys = Eq.cong (x ∷_) (lemma-append-∷ xs y ys)

------------------------------------------------------------------------
-- List quantification

module All where

  open import Data.List.Relation.Unary.All public using (All ; [] ; _∷_)

  -- All[ x ∈ xs ] B: every member of xs satisfies B.
  All′ : {A : Set} (P : A → Set) → List A → Set
  All′ = All

  infixr 3 All′
  syntax All′ (λ x → B) xs = All[ x ∈ xs ] B

  All-elim : ∀ {X : Set} {x : X} {xs} {P : X → Set} → mem x xs → All P xs → P x
  All-elim mem-head (x ∷ a) = x
  All-elim (mem-tail m) (y ∷ a) = All-elim m a

------------------------------------------------------------------------
-- Strict application
--
-- Apply k to xs after expanding xs strictly: a workaround for the
-- occasional inefficiency of Agda's evaluation.

module Strict where

  strict : {X : Set} {P : List X → Set} → (xs : List X) → (k : (xs : List X) → P xs) → P xs
  strict [] k = k []
  strict (x ∷ xs) k = strict xs (λ xs' → k (x ∷ xs'))

  lemma-strict : {X : Set} {P : List X → Set} → (xs : List X) → (k : (xs : List X) → P xs) → strict xs k ≡ k xs
  lemma-strict [] k = refl
  lemma-strict (x ∷ xs) k = lemma-strict xs (λ xs' → k (x ∷ xs'))

------------------------------------------------------------------------
-- Cancellation

lemma-list-cancellation-head : ∀ {X : Set} {x y : X} {xs ys : List X} → x ∷ xs ≡ y ∷ ys → x ≡ y
lemma-list-cancellation-head refl = refl

lemma-list-cancellation-tail : ∀ {X : Set} {x y : X} {xs ys : List X} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
lemma-list-cancellation-tail refl = refl

------------------------------------------------------------------------
-- Lists over a sum of alphabets

is-L-list : ∀ {A B} → List (A ∪ B) → Set
is-L-list {A} {B} xs = ∃ λ (xs' : List A) → map ⌜_ xs' ≡ xs

is-R-list : ∀ {A B} → List (A ∪ B) → Set
is-R-list {A} {B} xs = ∃ λ (xs' : List B) → map _⌝ xs' ≡ xs

take-while-isL : ∀ {A B} → (xs : List (A ∪ B)) → List (A ∪ B)
take-while-isL [] = []
take-while-isL (⌜ x ∷ xs) = ⌜ x ∷ take-while-isL xs
take-while-isL (x ⌝ ∷ xs) = []

take-while-isR : ∀ {A B} → (xs : List (A ∪ B)) → List (A ∪ B)
take-while-isR [] = []
take-while-isR (x ⌝ ∷ xs) = x ⌝ ∷ take-while-isR xs
take-while-isR (⌜ x ∷ xs) = []

drop-while-isL : ∀ {A B} → (xs : List (A ∪ B)) → List (A ∪ B)
drop-while-isL [] = []
drop-while-isL (⌜ x ∷ xs) = drop-while-isL xs
drop-while-isL (x ⌝ ∷ xs) = x ⌝ ∷ xs

drop-while-isR : ∀ {A B} → (xs : List (A ∪ B)) → List (A ∪ B)
drop-while-isR [] = []
drop-while-isR (x ⌝ ∷ xs) = drop-while-isR xs
drop-while-isR (⌜ x ∷ xs) = ⌜ x ∷ xs

lemma-take-drop-isL : ∀ {A B} → (xs : List (A ∪ B)) → take-while-isL xs ++ drop-while-isL xs ≡ xs
lemma-take-drop-isL [] = refl
lemma-take-drop-isL (⌜ x ∷ xs) = Eq.cong (⌜ x ∷_) (lemma-take-drop-isL xs)
lemma-take-drop-isL (x ⌝ ∷ xs) = refl

lemma-take-drop-isR : ∀ {A B} → (xs : List (A ∪ B)) → take-while-isR xs ++ drop-while-isR xs ≡ xs
lemma-take-drop-isR [] = refl
lemma-take-drop-isR (x ⌝ ∷ xs) = Eq.cong (x ⌝ ∷_) (lemma-take-drop-isR xs)
lemma-take-drop-isR (⌜ x ∷ xs) = refl

lemma-take-while-isL-isL : ∀ {A B} → (xs : List (A ∪ B)) → is-L-list (take-while-isL xs)
lemma-take-while-isL-isL [] = ([] , refl)
lemma-take-while-isL-isL (⌜ x ∷ xs) with lemma-take-while-isL-isL xs
... | x₁ , x₂ = x ∷ x₁ , Eq.cong (⌜ x ∷_) x₂
lemma-take-while-isL-isL (x ⌝ ∷ xs) = [] , refl

lemma-take-while-isR-isR : ∀ {A B} → (xs : List (A ∪ B)) → is-R-list (take-while-isR xs)
lemma-take-while-isR-isR [] = ([] , refl)
lemma-take-while-isR-isR (x ⌝ ∷ xs) with lemma-take-while-isR-isR xs
... | x₁ , x₂ = x ∷ x₁ , Eq.cong (x ⌝ ∷_) x₂
lemma-take-while-isR-isR (⌜ x ∷ xs) = [] , refl

-- Apply f to the maximal runs of left (right) letters.
lift-L' : ∀ {A B} → ℕ → (f : List A → List A) → List (A ∪ B) → List (A ∪ B)
lift-L' zero f xs = xs
lift-L' (suc n) f [] = []
lift-L' (suc n) f a@(⌜ x ∷ xs) = map ⌜_ (f (proj₁ (lemma-take-while-isL-isL a))) ++ lift-L' n f (drop-while-isL a)
lift-L' (suc n) f (x ⌝ ∷ xs) = x ⌝ ∷ lift-L' (suc n) f xs

lift-L : ∀ {A B} → (f : List A → List A) → List (A ∪ B) → List (A ∪ B)
lift-L f xs = lift-L' (length xs) f xs

lift-R' : ∀ {A B} → ℕ → (f : List B → List B) → List (A ∪ B) → List (A ∪ B)
lift-R' zero f xs = xs
lift-R' (suc n) f [] = []
lift-R' (suc n) f a@(x ⌝ ∷ xs) = map _⌝ (f (proj₁ (lemma-take-while-isR-isR a))) ++ lift-R' n f (drop-while-isR a)
lift-R' (suc n) f (⌜ x ∷ xs) = ⌜ x ∷ lift-R' (suc n) f xs

lift-R : ∀ {A B} → (f : List B → List B) → List (A ∪ B) → List (A ∪ B)
lift-R f xs = lift-R' (length xs) f xs

------------------------------------------------------------------------
-- Finiteness, and proofs by finite case analysis

module Finite where

  Finite : (X : Set) → Set
  Finite X = ∃ λ (xs : List X) → ∀ x → mem x xs

  lemma-finite-product : {X Y : Set} → Finite X → Finite Y → Finite (X × Y)
  lemma-finite-product (xs , x-enum) (ys , y-enum) = (zs , z-enum)
    where
    zs = concat (map (λ y → map (λ x → (x , y)) xs) ys)
    z-enum : ∀ z → mem z zs
    z-enum (x , y) = lemma-mem-list-prod xs ys (x-enum x) (y-enum y)

module By-Cases where

  open Finite
  open All

  by-finite-cases : {X : Set} → (fin : Finite X) → (x : X) → (B : X → Set) → All[ x ∈ proj₁ fin ] B x → B x
  by-finite-cases (xs , enum) x B hyp = All-elim (enum x) hyp

  lemma-list-equality : {X Y : Set} → (xs : List X) → (eq : X → Y × Y) → let eqs = map eq xs in
                        map proj₁ eqs ≡ map proj₂ eqs → All[ x ∈ xs ] proj₁ (eq x) ≡ proj₂ (eq x)
  lemma-list-equality [] eq hyp = []
  lemma-list-equality (x ∷ xs) eq hyp =
    lemma-list-cancellation-head hyp ∷ lemma-list-equality xs eq (lemma-list-cancellation-tail hyp)

  equality-by-cases : {X Y : Set} → (fin : Finite X) → (x : X) → (eq : X → Y × Y) →
                      let xs = proj₁ fin
                          eqs = map eq xs
                      in
                      map proj₁ eqs ≡ map proj₂ eqs → proj₁ (eq x) ≡ proj₂ (eq x)
  equality-by-cases fin x eq hyp =
    by-finite-cases fin x (λ x → proj₁ (eq x) ≡ proj₂ (eq x)) (lemma-list-equality (proj₁ fin) eq hyp)

------------------------------------------------------------------------
-- Semi-decidable equality

record MaybeEq (A : Set) : Set where
  infixl 4 _=m?_
  field
    _=m?_ : (x y : A) → Maybe (x ≡ y)

open MaybeEq {{...}} public

instance
  MaybeEq-ℕ : MaybeEq ℕ
  MaybeEq-ℕ ._=m?_ = go
    where
    go : (x y : ℕ) → Maybe (x ≡ y)
    go zero zero = just refl
    go zero (suc y) = nothing
    go (suc x) zero = nothing
    go (suc x) (suc y) with go x y
    ... | just e = just (Eq.cong suc e)
    ... | nothing = nothing

  MaybeEq-List : ∀ {A} → {{MaybeEq A}} → MaybeEq (List A)
  MaybeEq-List {A} ._=m?_ = go
    where
    go : (xs ys : List A) → Maybe (xs ≡ ys)
    go [] [] = just refl
    go [] (y ∷ ys) = nothing
    go (x ∷ xs) [] = nothing
    go (x ∷ xs) (y ∷ ys) with x =m? y | go xs ys
    ... | just e | just e′ = just (Eq.cong₂ _∷_ e e′)
    ... | _ | _ = nothing

  MaybeEq-∪ : ∀ {A B} → {{MaybeEq A}} → {{MaybeEq B}} → MaybeEq (A ∪ B)
  MaybeEq-∪ {A} {B} ._=m?_ = go
    where
    go : (x y : A ∪ B) → Maybe (x ≡ y)
    go (⌜ x) (⌜ y) with x =m? y
    ... | just refl = just refl
    ... | nothing = nothing
    go (⌜ x) (y ⌝) = nothing
    go (x ⌝) (⌜ y) = nothing
    go (x ⌝) (y ⌝) with x =m? y
    ... | just refl = just refl
    ... | nothing = nothing

------------------------------------------------------------------------
-- Maybe

isJust : {A : Set} → Maybe A → Bool
isJust (just x) = true
isJust nothing = false

fromJust : {A : Set} (x : Maybe A) → isJust x ≡ true → A
fromJust (just x) hyp = x
fromJust nothing ()
