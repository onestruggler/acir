------------------------------------------------------------------------
-- Presentations of groups
--
-- Derivations as data, checked by one evaluation.
--
-- Presentation.Rewrite proves each equation of a derivation by its own
-- definition, closed by refl.  For a derivation of tens of thousands of
-- equations, spread over modules, Agda then loads the interfaces of
-- every module an equation cites, and the time goes into loading them.
-- Here a whole derivation is one value, a certificate: a list of facts,
-- each a pair of words with how it is obtained, and `certify` checks it
-- by one evaluation.  A fact is either a norm step, two words over a
-- smaller alphabet with one semantics (`norm`, given a completeness
-- for that alphabet), or a chain of rewrites (`steps`), each rewriting
-- at a position by an earlier fact (by its index) or by a supplied
-- equation (`ax`), forwards or backwards.  The facts proved so far are
-- kept in a binary trie keyed by the bits of their index.  The targets
-- are equations the certificate must contain, with the index of the
-- fact that proves each; `certify-sound` turns a passed check into a
-- proof of every target.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel)

module Presentation.Certificate
  {A : Set} (Γ : WRel A)
  (eqA : A → A → Bool) (eqA-sound : ∀ x y → eqA x y ≡ true → x ≡ y)
  where

open import Data.List.Base using (List ; [] ; _∷_ ; map ; _++_ ; length ; take ; drop)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _/_ ; _%_ ; _≡ᵇ_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
import Presentation.Base as PB

open import Presentation.Rewrite Γ eqA eqA-sound public
  using (⟪_⟫ ; Eqn ; eqn ; lhs ; rhs ; prf ; eqL ; eqL-sound)
open import Presentation.Rewrite Γ eqA eqA-sound
  using (rewrite-at ; matches-at ; rw-sound)
open PB Γ using (_≈_ ; refl ; sym ; trans)

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = Eq.refl

  ∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
  ∧-r true h = h

  just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
  just-inj Eq.refl = Eq.refl

------------------------------------------------------------------------
-- A trie of word pairs, keyed by lists of bits

Pair : Set
Pair = List A × List A

data Trie : Set where
  leaf : Trie
  node : Maybe Pair → Trie → Trie → Trie

lookupT : Trie → List Bool → Maybe Pair
lookupT leaf         _           = nothing
lookupT (node v l r) []          = v
lookupT (node v l r) (false ∷ k) = lookupT l k
lookupT (node v l r) (true  ∷ k) = lookupT r k

insertT : Trie → List Bool → Pair → Trie
insertT leaf         []          p = node (just p) leaf leaf
insertT leaf         (false ∷ k) p = node nothing (insertT leaf k p) leaf
insertT leaf         (true  ∷ k) p = node nothing leaf (insertT leaf k p)
insertT (node v l r) []          p = node (just p) l r
insertT (node v l r) (false ∷ k) p = node v (insertT l k p) r
insertT (node v l r) (true  ∷ k) p = node v l (insertT r k p)

-- What a lookup after an insert finds: the new pair or an old one.
lookup-insert : ∀ t k p k′ w → lookupT (insertT t k p) k′ ≡ just w →
                (w ≡ p) ⊎ (lookupT t k′ ≡ just w)
lookup-insert leaf [] p [] w h = inj₁ (Eq.sym (just-inj h))
lookup-insert leaf [] p (false ∷ k′) w ()
lookup-insert leaf [] p (true ∷ k′) w ()
lookup-insert leaf (false ∷ k) p [] w ()
lookup-insert leaf (false ∷ k) p (false ∷ k′) w h with lookup-insert leaf k p k′ w h
... | inj₁ e  = inj₁ e
... | inj₂ ()
lookup-insert leaf (false ∷ k) p (true ∷ k′) w ()
lookup-insert leaf (true ∷ k) p [] w ()
lookup-insert leaf (true ∷ k) p (false ∷ k′) w ()
lookup-insert leaf (true ∷ k) p (true ∷ k′) w h with lookup-insert leaf k p k′ w h
... | inj₁ e  = inj₁ e
... | inj₂ ()
lookup-insert (node v l r) [] p [] w h = inj₁ (Eq.sym (just-inj h))
lookup-insert (node v l r) [] p (false ∷ k′) w h = inj₂ h
lookup-insert (node v l r) [] p (true ∷ k′) w h = inj₂ h
lookup-insert (node v l r) (false ∷ k) p [] w h = inj₂ h
lookup-insert (node v l r) (false ∷ k) p (false ∷ k′) w h = lookup-insert l k p k′ w h
lookup-insert (node v l r) (false ∷ k) p (true ∷ k′) w h = inj₂ h
lookup-insert (node v l r) (true ∷ k) p [] w h = inj₂ h
lookup-insert (node v l r) (true ∷ k) p (false ∷ k′) w h = inj₂ h
lookup-insert (node v l r) (true ∷ k) p (true ∷ k′) w h = lookup-insert r k p k′ w h

-- The key of a fact: the bits of its index, least significant first.
bits : ℕ → ℕ → List Bool
bits zero    _ = []
bits (suc f) n = (n % 2 ≡ᵇ 1) ∷ bits f (n / 2)

key : ℕ → List Bool
key = bits 24

-- Every pair in the trie is an equation.
record Valid (t : Trie) : Set where
  constructor valid
  field get : ∀ k w → lookupT t k ≡ just w → ⟪ proj₁ w ⟫ ≈ ⟪ proj₂ w ⟫
open Valid

valid-leaf : Valid leaf
valid-leaf = valid λ k w ()

valid-insert : ∀ {t} k p → Valid t → ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫ → Valid (insertT t k p)
valid-insert {t} k p vt e = valid get′
  where
  get′ : ∀ k′ w → lookupT (insertT t k p) k′ ≡ just w → ⟪ proj₁ w ⟫ ≈ ⟪ proj₂ w ⟫
  get′ k′ w h with lookup-insert t k p k′ w h
  ... | inj₁ Eq.refl = e
  ... | inj₂ h′      = get vt k′ w h′

------------------------------------------------------------------------
-- Certificates

data Src : Set where
  fact : ℕ → Src       -- an earlier fact, by its index
  ax   : ℕ → Src       -- a supplied equation

record StepC : Set where
  constructor st
  field
    pos : ℕ
    src : Src
    fwd : Bool

-- A fact: a norm step between words over a smaller alphabet B, or two
-- words with a chain of rewrites.
data FactC (B : Set) : Set where
  norm  : List B → List B → FactC B
  steps : List A → List A → List StepC → FactC B

module Checker
  {B : Set} (ιB : B → A)
  -- a decision for norm steps between words over B, and its soundness
  (normOK : List B → List B → Bool)
  (normOK-sound : ∀ u v → normOK u v ≡ true → ⟪ map ιB u ⟫ ≈ ⟪ map ιB v ⟫)
  -- the supplied equations
  (axE : ℕ → Maybe Eqn)
  where

  pairOf : FactC B → Pair
  pairOf (norm u v)      = map ιB u , map ιB v
  pairOf (steps l r _)   = l , r

  private
    fromEqn : Maybe Eqn → Maybe Pair
    fromEqn nothing  = nothing
    fromEqn (just e) = just (lhs e , rhs e)

    orient : Bool → Pair → Pair
    orient true  p       = p
    orient false (l , r) = r , l

  resolve : Trie → Src → Maybe Pair
  resolve t (fact i) = lookupT t (key i)
  resolve t (ax j)   = fromEqn (axE j)


  -- Matching and rewriting by a pair: Presentation.Rewrite's, which
  -- read only the two sides of an equation.
  matchP : ℕ → List A → List A → Bool
  matchP i l xs = eqL (take (length l) (drop i xs)) l

  rewriteP : ℕ → List A → List A → List A → List A
  rewriteP i l r xs = take i xs ++ (r ++ drop (length l) (drop i xs))

  rwP-sound : ∀ i l r xs → ⟪ l ⟫ ≈ ⟪ r ⟫ → matchP i l xs ≡ true →
              ⟪ xs ⟫ ≈ ⟪ rewriteP i l r xs ⟫
  rwP-sound i l r xs e h = rw-sound i (eqn l r e) xs h

  runC     : Trie → List StepC → List A → Maybe (List A)
  resolved : Trie → ℕ → Bool → Maybe Pair → List StepC → List A → Maybe (List A)
  applyB   : Bool → Trie → ℕ → Pair → List StepC → List A → Maybe (List A)

  runC t []              xs = just xs
  runC t (st i s f ∷ ss) xs = resolved t i f (resolve t s) ss xs

  resolved t i f nothing  ss xs = nothing
  resolved t i f (just p) ss xs =
    applyB (matchP i (proj₁ (orient f p)) xs) t i (orient f p) ss xs

  applyB false t i p       ss xs = nothing
  applyB true  t i (l , r) ss xs = runC t ss (rewriteP i l r xs)

  eqM : Maybe (List A) → List A → Bool
  eqM nothing   _ = false
  eqM (just xs) r = eqL xs r

  checkFact : Trie → FactC B → Bool
  checkFact t (norm u v)     = normOK u v
  checkFact t (steps l r ss) = eqM (runC t ss l) r

  go  : ℕ → Trie → List (FactC B) → Maybe Trie
  goB : Bool → ℕ → Trie → FactC B → List (FactC B) → Maybe Trie

  go i t []       = just t
  go i t (f ∷ fs) = goB (checkFact t f) i t f fs

  goB false i t f fs = nothing
  goB true  i t f fs = go (suc i) (insertT t (key i) (pairOf f)) fs

  -- A target: the index of a fact, and the equation it must be.
  Target : Set
  Target = ℕ × Pair

  eqPair : Pair → Pair → Bool
  eqPair (l , r) (l′ , r′) = eqL l l′ ∧ eqL r r′

  eqMP : Maybe Pair → Pair → Bool
  eqMP nothing  _ = false
  eqMP (just q) p = eqPair q p

  allHit : Trie → List Target → Bool
  allHit t []             = true
  allHit t ((i , p) ∷ ts) = eqMP (lookupT t (key i)) p ∧ allHit t ts

  fin : Maybe Trie → List Target → Bool
  fin nothing  ts = false
  fin (just t) ts = allHit t ts

  certify : List (FactC B) → List Target → Bool
  certify cert ts = fin (go 0 leaf cert) ts

  ----------------------------------------------------------------------
  -- Soundness

  private
    orient-sound : ∀ f p → ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫ →
                   ⟪ proj₁ (orient f p) ⟫ ≈ ⟪ proj₂ (orient f p) ⟫
    orient-sound true  p       e = e
    orient-sound false (l , r) e = sym e

    fromEqn-sound : ∀ m p → fromEqn m ≡ just p → ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫
    fromEqn-sound (just e) p Eq.refl = prf e

  resolve-sound : ∀ {t} → Valid t → ∀ s p → resolve t s ≡ just p →
                  ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫
  resolve-sound vt (fact i) p h = get vt (key i) p h
  resolve-sound vt (ax j)   p h = fromEqn-sound (axE j) p h

  runC-sound     : ∀ {t} → Valid t → ∀ ss xs ys → runC t ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  resolved-sound : ∀ {t} → Valid t → ∀ i f m ss xs ys →
                   (∀ p → m ≡ just p → ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫) →
                   resolved t i f m ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  applyB-sound   : ∀ {t} → Valid t → ∀ b i p ss xs ys → ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫ →
                   matchP i (proj₁ p) xs ≡ b →
                   applyB b t i p ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫

  runC-sound vt []              xs ys Eq.refl = refl
  runC-sound {t} vt (st i s f ∷ ss) xs ys h =
    resolved-sound vt i f (resolve t s) ss xs ys (λ p e → resolve-sound vt s p e) h

  resolved-sound vt i f (just p) ss xs ys mp h =
    applyB-sound vt _ i (orient f p) ss xs ys (orient-sound f p (mp p Eq.refl)) Eq.refl h

  applyB-sound vt true i (l , r) ss xs ys e m h =
    trans (rwP-sound i l r xs e m) (runC-sound vt ss (rewriteP i l r xs) ys h)

  private
    eqM-sound : ∀ m r → eqM m r ≡ true → m ≡ just r
    eqM-sound (just xs) r h = Eq.cong just (eqL-sound xs r h)

  checkFact-sound : ∀ {t} → Valid t → ∀ f → checkFact t f ≡ true →
                    ⟪ proj₁ (pairOf f) ⟫ ≈ ⟪ proj₂ (pairOf f) ⟫
  checkFact-sound vt (norm u v)     h = normOK-sound u v h
  checkFact-sound vt (steps l r ss) h = runC-sound vt ss l r (eqM-sound (runC _ ss l) r h)

  go-sound  : ∀ {t} → Valid t → ∀ i fs T → go i t fs ≡ just T → Valid T
  goB-sound : ∀ {t} → Valid t → ∀ b i f fs T → checkFact t f ≡ b →
              goB b i t f fs ≡ just T → Valid T

  go-sound vt i []       T Eq.refl = vt
  go-sound {t} vt i (f ∷ fs) T h = goB-sound vt (checkFact t f) i f fs T Eq.refl h

  goB-sound {t} vt true i f fs T c h =
    go-sound (valid-insert (key i) (pairOf f) vt (checkFact-sound vt f c)) (suc i) fs T h

  -- What a passed check proves: every target.
  data AllEq : List Target → Set where
    []  : AllEq []
    _∷_ : ∀ {i p ts} → ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫ → AllEq ts → AllEq ((i , p) ∷ ts)

  private
    eqPair-sound : ∀ q p → eqPair q p ≡ true → q ≡ p
    eqPair-sound (l , r) (l′ , r′) h =
      Eq.cong₂ _,_ (eqL-sound l l′ (∧-l h)) (eqL-sound r r′ (∧-r (eqL l l′) h))

    eqMP-sound : ∀ m p → eqMP m p ≡ true → m ≡ just p
    eqMP-sound (just q) p h = Eq.cong just (eqPair-sound q p h)

    allHit-sound : ∀ {t} → Valid t → ∀ ts → allHit t ts ≡ true → AllEq ts
    allHit-sound vt []             h = []
    allHit-sound {t} vt ((i , p) ∷ ts) h =
      get vt (key i) p (eqMP-sound (lookupT t (key i)) p (∧-l h))
      ∷ allHit-sound vt ts (∧-r (eqMP (lookupT t (key i)) p) h)

    fin-sound : ∀ m ts → (∀ T → m ≡ just T → Valid T) → fin m ts ≡ true → AllEq ts
    fin-sound (just T) ts vm h = allHit-sound (vm T Eq.refl) ts h

  certify-sound : ∀ cert ts → certify cert ts ≡ true → AllEq ts
  certify-sound cert ts h =
    fin-sound (go 0 leaf cert) ts (λ T e → go-sound valid-leaf 0 cert T e) h

  -- The k-th target as an equation.  Its sides come from the target list
  -- alone, so reading them does not evaluate the certificate.
  target : (ts : List Target) → AllEq ts → ℕ → Eqn
  target []             _ _       = eqn [] [] refl
  target ((i , p) ∷ ts) h zero    = eqn (proj₁ p) (proj₂ p) (head h)
    where
    head : ∀ {i p ts} → AllEq ((i , p) ∷ ts) → ⟪ proj₁ p ⟫ ≈ ⟪ proj₂ p ⟫
    head (e ∷ _) = e
  target ((i , p) ∷ ts) h (suc k) = target ts (tail h) k
    where
    tail : ∀ {i p ts} → AllEq ((i , p) ∷ ts) → AllEq ts
    tail (_ ∷ es) = es
