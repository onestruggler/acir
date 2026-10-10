------------------------------------------------------------------------
-- Presentations of groups
--
-- The pivot column under X[j,j+1], for Case 1 of Lemma 4.4.
--
-- X[j,j′] with j′ = j + 1 swaps two adjacent entries, so every other
-- index lies on the same side of both.  Hence the first odd entry i₁
-- and the next one i₂ in its class move only when j or j′ is one of
-- them, as Clément's subcases say:
--
-- * 1.4: neither is j or j′, and they stay (fo-out, ns-out);
-- * 1.10: (i₁, i₂) = (j, j′) stays (fo-jj, ns-jj);
-- * 1.11: i₁ = j < j′ < i₂: i₁ becomes j′ when entry j′ is even
--   (1.11.1: fo-to-j′, ns-to-j′); when it is odd, of the other class,
--   i₁ stays and its partner becomes that of j′ (1.11.2: fo-jj,
--   ns-from-j′);
-- * 1.12: i₁ = j′ becomes j (fo-from-j′, ns-from-j′);
-- * 1.13: i₂ = j′ (i₁ < j) becomes j (ns-to-j);
-- * 1.14: i₂ = j (i₁ < j) becomes j′, unless entry j′ is in the class
--   of i₁ (1.14.1: ns-j-to-j′; 1.14.2: ns-j-keep).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base as Fin using (Fin ; toℕ ; _<_)
open import Data.Nat.Base as ℕ using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Swap
  {n : ℕ} {j j′ : Fin n} (adj : toℕ j′ ≡ suc (toℕ j)) where

open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (just)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Nullary using (¬_)

open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (Z ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; Odd ; Even)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
  using (firstOdd ; nextSame ; Same ; firstOdd-char ; firstOdd-spec ; nextSame-char ; nextSame-spec)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Xᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (set₂-a ; set₂-b ; set₂-≢)

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

jj′ : j < j′
jj′ = ≡.subst (toℕ j ℕ.<_) (≡.sym adj) (ℕP.n<1+n (toℕ j))

j≢j′ : j ≢ j′
j≢j′ = <-≢ jj′

------------------------------------------------------------------------
-- Adjacency: no index lies strictly between j and j′

lt-j′ : ∀ {x : Fin n} → x ≢ j → x < j′ → x < j
lt-j′ {x} x≢j x<j′ =
  ℕP.≤∧≢⇒< (ℕP.≤-pred (≡.subst (toℕ x ℕ.<_) adj x<j′)) (λ e → x≢j (FinP.toℕ-injective e))

gt-j : ∀ {x : Fin n} → x ≢ j′ → j < x → j′ < x
gt-j {x} x≢j′ j<x = ℕP.≤∧≢⇒< (≡.subst (ℕ._≤ toℕ x) (≡.sym adj) j<x) (λ e → x≢j′ (FinP.toℕ-injective (≡.sym e)))

lt-j : ∀ {x : Fin n} → x < j → x < j′
lt-j x<j = ℕP.<-trans x<j jj′

gt-j′ : ∀ {x : Fin n} → j′ < x → j < x
gt-j′ j′<x = ℕP.<-trans jj′ j′<x

none-between : ∀ {x : Fin n} → j < x → x < j′ → ⊥
none-between {x} j<x x<j′ = ℕP.<-asym j<x (lt-j′ (sym≢ (<-≢ j<x)) x<j′)

------------------------------------------------------------------------
-- The entries

module _ (w : Vec Z n) where

  private
    w′ : Vec Z n
    w′ = Xᶻ j j′ w

  sw-j : w′ ! j ≡ w ! j′
  sw-j = set₂-a j j′ (w ! j′) (w ! j) w

  sw-j′ : w′ ! j′ ≡ w ! j
  sw-j′ = set₂-b j j′ (w ! j′) (w ! j) w j≢j′

  sw-o : ∀ {x} → x ≢ j → x ≢ j′ → w′ ! x ≡ w ! x
  sw-o x≢j x≢j′ = set₂-≢ j j′ (w ! j′) (w ! j) w x≢j x≢j′

  private
    odd≡ : ∀ {x y} → w′ ! x ≡ w ! y → oddᶻ (w′ ! x) ≡ oddᶻ (w ! y)
    odd≡ e = ≡.cong oddᶻ e

    -- Same transported along equal entries.
    same≡ : ∀ {i x i′ x′} → w′ ! i ≡ w ! i′ → w′ ! x ≡ w ! x′ → Same w′ i x → Same w i′ x′
    same≡ ei ex (o , r) = ≡.trans (≡.sym (≡.cong oddᶻ ex)) o , ≡.trans (≡.sym (≡.cong rbit ex)) (≡.trans r (≡.cong rbit ei))

    same≡′ : ∀ {i x i′ x′} → w′ ! i ≡ w ! i′ → w′ ! x ≡ w ! x′ → Same w i′ x′ → Same w′ i x
    same≡′ ei ex (o , r) = ≡.trans (≡.cong oddᶻ ex) o , ≡.trans (≡.cong rbit ex) (≡.trans r (≡.sym (≡.cong rbit ei)))

  ----------------------------------------------------------------------
  -- 1.4: i₁ and i₂ apart from j and j′

  fo-out : ∀ {i} → firstOdd w ≡ just i → i ≢ j → i ≢ j′ → firstOdd w′ ≡ just i
  fo-out {i} fo i≢j i≢j′ = firstOdd-char w′ (≡.trans (odd≡ (sw-o i≢j i≢j′)) (proj₁ spec)) below
    where
    spec = firstOdd-spec w fo
    below : ∀ x → x < i → Even (w′ ! x)
    below x x<i = dec-elim (x FinP.≟ j)
      (λ { ≡.refl → ≡.trans (odd≡ sw-j) (proj₂ spec j′ (gt-j i≢j′ x<i)) })
      (λ x≢j → dec-elim (x FinP.≟ j′)
        (λ { ≡.refl → ≡.trans (odd≡ sw-j′) (proj₂ spec j (ℕP.<-trans jj′ x<i)) })
        (λ x≢j′ → ≡.trans (odd≡ (sw-o x≢j x≢j′)) (proj₂ spec x x<i)))

  ns-out : ∀ {i i₂} → nextSame i w ≡ just i₂ → i ≢ j → i ≢ j′ → i₂ ≢ j → i₂ ≢ j′ → nextSame i w′ ≡ just i₂
  ns-out {i} {i₂} nx i≢j i≢j′ i₂≢j i₂≢j′ =
    nextSame-char w′ (proj₁ spec) (same≡′ (sw-o i≢j i≢j′) (sw-o i₂≢j i₂≢j′) (proj₁ (proj₂ spec))) between
    where
    spec = nextSame-spec w nx
    between : ∀ x → i < x → x < i₂ → ¬ Same w′ i x
    between x i<x x<i₂ s = dec-elim (x FinP.≟ j)
      (λ { ≡.refl → proj₂ (proj₂ spec) j′ (lt-j i<x) (gt-j′′ x<i₂) (same≡ (sw-o i≢j i≢j′) sw-j s) })
      (λ x≢j → dec-elim (x FinP.≟ j′)
        (λ { ≡.refl → proj₂ (proj₂ spec) j (lt-j′ (i≢j) i<x) (ℕP.<-trans jj′ x<i₂) (same≡ (sw-o i≢j i≢j′) sw-j′ s) })
        (λ x≢j′ → proj₂ (proj₂ spec) x i<x x<i₂ (same≡ (sw-o i≢j i≢j′) (sw-o x≢j x≢j′) s)))
      where
      -- j < i₂ and i₂ ≠ j′ give j′ < i₂.
      gt-j′′ : j < i₂ → j′ < i₂
      gt-j′′ = gt-j i₂≢j′

  ----------------------------------------------------------------------
  -- 1.10, 1.11.2: entry j odd, and entry j′ odd

  fo-jj : firstOdd w ≡ just j → Odd (w ! j′) → firstOdd w′ ≡ just j
  fo-jj fo oj′ = firstOdd-char w′ (≡.trans (odd≡ sw-j) oj′) below
    where
    below : ∀ x → x < j → Even (w′ ! x)
    below x x<j = ≡.trans (odd≡ (sw-o (<-≢ x<j) (<-≢ (lt-j x<j)))) (proj₂ (firstOdd-spec w fo) x x<j)

  ns-jj : Odd (w ! j) → nextSame j w ≡ just j′ → nextSame j w′ ≡ just j′
  ns-jj oj nx = nextSame-char w′ jj′ same (λ x j<x x<j′ _ → none-between j<x x<j′)
    where
    s = proj₁ (proj₂ (nextSame-spec w nx))
    same : Same w′ j j′
    same = ≡.trans (odd≡ sw-j′) oj , ≡.trans (≡.cong rbit sw-j′) (≡.trans (≡.sym (proj₂ s)) (≡.sym (≡.cong rbit sw-j)))

  ----------------------------------------------------------------------
  -- 1.11.1: i₁ = j and entry j′ even

  fo-to-j′ : firstOdd w ≡ just j → Even (w ! j′) → firstOdd w′ ≡ just j′
  fo-to-j′ fo ej′ = firstOdd-char w′ (≡.trans (odd≡ sw-j′) (proj₁ (firstOdd-spec w fo))) below
    where
    below : ∀ x → x < j′ → Even (w′ ! x)
    below x x<j′ = dec-elim (x FinP.≟ j)
      (λ { ≡.refl → ≡.trans (odd≡ sw-j) ej′ })
      (λ x≢j → ≡.trans (odd≡ (sw-o x≢j (<-≢ x<j′))) (proj₂ (firstOdd-spec w fo) x (lt-j′ x≢j x<j′)))

  ns-to-j′ : ∀ {i₂} → nextSame j w ≡ just i₂ → j′ < i₂ → nextSame j′ w′ ≡ just i₂
  ns-to-j′ {i₂} nx j′<i₂ = nextSame-char w′ j′<i₂ (same≡′ sw-j′ (sw-o i₂≢j i₂≢j′) (proj₁ (proj₂ spec))) between
    where
    spec = nextSame-spec w nx
    i₂≢j′ = sym≢ (<-≢ j′<i₂)
    i₂≢j = sym≢ (<-≢ (ℕP.<-trans jj′ j′<i₂))
    between : ∀ x → j′ < x → x < i₂ → ¬ Same w′ j′ x
    between x j′<x x<i₂ s =
      proj₂ (proj₂ spec) x (gt-j′ j′<x) x<i₂
        (same≡ sw-j′ (sw-o (sym≢ (<-≢ (gt-j′ j′<x))) (sym≢ (<-≢ j′<x))) s)

  ----------------------------------------------------------------------
  -- 1.11.2, 1.12: the partner of j′ becomes that of j

  ns-from-j′ : ∀ {b} → ¬ Same w j′ j → nextSame j′ w ≡ just b → nextSame j w′ ≡ just b
  ns-from-j′ {b} ¬s nx = nextSame-char w′ (gt-j′ (proj₁ spec)) (same≡′ sw-j (sw-o b≢j b≢j′) (proj₁ (proj₂ spec))) between
    where
    spec = nextSame-spec w nx
    b≢j′ = sym≢ (<-≢ (proj₁ spec))
    b≢j = sym≢ (<-≢ (gt-j′ (proj₁ spec)))
    between : ∀ x → j < x → x < b → ¬ Same w′ j x
    between x j<x x<b s = dec-elim (x FinP.≟ j′)
      (λ { ≡.refl → ¬s (same≡ sw-j sw-j′ s) })
      (λ x≢j′ → proj₂ (proj₂ spec) x (gt-j x≢j′ j<x) x<b (same≡ sw-j (sw-o (sym≢ (<-≢ j<x)) x≢j′) s))

  fo-from-j′ : firstOdd w ≡ just j′ → firstOdd w′ ≡ just j
  fo-from-j′ fo = firstOdd-char w′ (≡.trans (odd≡ sw-j) (proj₁ (firstOdd-spec w fo))) below
    where
    below : ∀ x → x < j → Even (w′ ! x)
    below x x<j = ≡.trans (odd≡ (sw-o (<-≢ x<j) (<-≢ (lt-j x<j)))) (proj₂ (firstOdd-spec w fo) x (lt-j x<j))

  ----------------------------------------------------------------------
  -- 1.13, 1.14: i₁ < j, and i₂ = j′ or i₂ = j

  ns-to-j : ∀ {i} → nextSame i w ≡ just j′ → i < j → nextSame i w′ ≡ just j
  ns-to-j {i} nx i<j = nextSame-char w′ i<j (same≡′ (sw-o (<-≢ i<j) (<-≢ (lt-j i<j))) sw-j (proj₁ (proj₂ spec))) between
    where
    spec = nextSame-spec w nx
    between : ∀ x → i < x → x < j → ¬ Same w′ i x
    between x i<x x<j s =
      proj₂ (proj₂ spec) x i<x (lt-j x<j) (same≡ (sw-o (<-≢ i<j) (<-≢ (lt-j i<j))) (sw-o (<-≢ x<j) (<-≢ (lt-j x<j))) s)

  ns-j-to-j′ : ∀ {i} → nextSame i w ≡ just j → ¬ Same w i j′ → nextSame i w′ ≡ just j′
  ns-j-to-j′ {i} nx ¬s = nextSame-char w′ (lt-j i<j) (same≡′ ei sw-j′ (proj₁ (proj₂ spec))) between
    where
    spec = nextSame-spec w nx
    i<j = proj₁ spec
    ei : w′ ! i ≡ w ! i
    ei = sw-o (<-≢ i<j) (<-≢ (lt-j i<j))
    between : ∀ x → i < x → x < j′ → ¬ Same w′ i x
    between x i<x x<j′ s = dec-elim (x FinP.≟ j)
      (λ { ≡.refl → ¬s (same≡ ei sw-j s) })
      (λ x≢j → proj₂ (proj₂ spec) x i<x (lt-j′ x≢j x<j′) (same≡ ei (sw-o x≢j (<-≢ x<j′)) s))

  ns-j-keep : ∀ {i} → nextSame i w ≡ just j → Same w i j′ → nextSame i w′ ≡ just j
  ns-j-keep {i} nx s′ = nextSame-char w′ i<j (same≡′ ei sw-j s′) between
    where
    spec = nextSame-spec w nx
    i<j = proj₁ spec
    ei : w′ ! i ≡ w ! i
    ei = sw-o (<-≢ i<j) (<-≢ (lt-j i<j))
    between : ∀ x → i < x → x < j → ¬ Same w′ i x
    between x i<x x<j s = proj₂ (proj₂ spec) x i<x x<j (same≡ ei (sw-o (<-≢ x<j) (<-≢ (lt-j x<j))) s)
