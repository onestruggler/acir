------------------------------------------------------------------------
-- Presentations of groups
--
-- Two numerals below eight avoiding a list
--
-- Figure 10's (71) holds for *any* six indices, and the paper's proof
-- of its degenerate cases routes through "the two smallest elements of
-- {0, …, N − 1} \ {a, b, c, d, e, f}".  Six blocked values out of the
-- eight numerals every width has leave two free, but that is a
-- pigeonhole, and a search with fuel does not prove it.
--
-- So the two are found by *deletion* instead: start from the list
-- 0 … 7, delete each blocked value in turn, and read the first two
-- survivors off.  Deleting one value shortens a strictly increasing
-- list by at most one — that is the whole of the counting — and a
-- survivor is by construction in the original list and different from
-- everything deleted.
--
-- Nothing here mentions the theory; it is arithmetic on lists.  Each
-- decision is taken by a helper taking the `Dec` rather than by a
-- `with`, so that a proof can case on it and see both branches reduce.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Avoid where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; length)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; ≤-reflexive ; m≤n⇒m≤1+n ; +-identityʳ ; +-suc
       ; <⇒≢ ; ≤-pred ; _≟_ ; <-trans)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)

------------------------------------------------------------------------
-- Membership, and strictly increasing lists

infix 4 _∈_

data _∈_ : ℕ → List ℕ → Set where
  here  : ∀ {x xs}   → x ∈ (x ∷ xs)
  there : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- `Up n xs`: the list increases strictly and starts at or above n.
data Up : ℕ → List ℕ → Set where
  nil  : ∀ {n} → Up n []
  cons : ∀ {n x xs} → n ≤ x → Up (suc x) xs → Up n (x ∷ xs)

Up-weaken : ∀ {n n′ : ℕ} {xs : List ℕ} → n ≤ n′ → Up n′ xs → Up n xs
Up-weaken le nil           = nil
Up-weaken le (cons le′ up) = cons (≤-trans le le′) up

-- So every member is at least the bound.
Up-≤ : ∀ {n : ℕ} {xs : List ℕ} {z : ℕ} → Up n xs → z ∈ xs → n ≤ z
Up-≤ (cons le up) here        = le
Up-≤ (cons le up) (there mem) = ≤-trans (m≤n⇒m≤1+n le) (Up-≤ up mem)

------------------------------------------------------------------------
-- Deleting one value

private
  step : ∀ {x y : ℕ} → Dec (x ≡ y) → ℕ → List ℕ → List ℕ
  step (yes _) x r = r
  step (no  _) x r = x ∷ r

flt : ℕ → List ℕ → List ℕ
flt y []       = []
flt y (x ∷ xs) = step (x ≟ y) x (flt y xs)

-- A survivor was there before, and is not the deleted value.
flt-∈ : ∀ (y : ℕ) (xs : List ℕ) {z : ℕ} → z ∈ flt y xs → (z ∈ xs) × (z ≢ y)
flt-∈ y (x ∷ xs) mem = go (x ≟ y) mem
  where
  go : ∀ (d : Dec (x ≡ y)) {w : ℕ} →
       w ∈ step d x (flt y xs) → (w ∈ (x ∷ xs)) × (w ≢ y)
  go (yes _) m         = there (proj₁ (flt-∈ y xs m)) , proj₂ (flt-∈ y xs m)
  go (no ne) here      = here , ne
  go (no ne) (there m) = there (proj₁ (flt-∈ y xs m)) , proj₂ (flt-∈ y xs m)

private
  -- Deleting a value the list does not hold changes nothing.
  flt-id : ∀ (y : ℕ) (xs : List ℕ) → (∀ {z : ℕ} → z ∈ xs → z ≢ y) →
           flt y xs ≡ xs
  flt-id y []       off = Eq.refl
  flt-id y (x ∷ xs) off = go (x ≟ y)
    where
    go : ∀ (d : Dec (x ≡ y)) → step d x (flt y xs) ≡ x ∷ xs
    go (yes e) = ⊥-elim (off here e)
    go (no  _) = Eq.cong (x ∷_) (flt-id y xs (λ mem → off (there mem)))

-- Deleting shortens a strictly increasing list by at most one.
flt-len : ∀ {n : ℕ} (y : ℕ) (xs : List ℕ) → Up n xs →
          length xs ≤ suc (length (flt y xs))
flt-len y []       up           = z≤n
flt-len y (x ∷ xs) (cons le up) = go (x ≟ y)
  where
  -- Above x every entry is above y too, so nothing else goes.
  gone : ∀ (w : ℕ) → x ≡ w → length xs ≤ length (flt w xs)
  gone w Eq.refl =
    ≤-reflexive (Eq.sym (Eq.cong length
      (flt-id w xs (λ mem e → <⇒≢ (Up-≤ up mem) (Eq.sym e)))))

  go : ∀ (d : Dec (x ≡ y)) →
       suc (length xs) ≤ suc (length (step d x (flt y xs)))
  go (yes e) = s≤s (gone y e)
  go (no  _) = s≤s (flt-len y xs up)

flt-Up : ∀ {n : ℕ} (y : ℕ) (xs : List ℕ) → Up n xs → Up n (flt y xs)
flt-Up         y []       up           = nil
flt-Up {n = n} y (x ∷ xs) (cons le up) = go (x ≟ y)
  where
  go : ∀ (d : Dec (x ≡ y)) → Up n (step d x (flt y xs))
  go (yes _) = Up-weaken (≤-trans le (m≤n⇒m≤1+n ≤-refl)) (flt-Up y xs up)
  go (no  _) = cons le (flt-Up y xs up)

------------------------------------------------------------------------
-- Deleting a whole list

minus : List ℕ → List ℕ → List ℕ
minus cs []       = cs
minus cs (b ∷ bs) = minus (flt b cs) bs

minus-∈ : ∀ (cs bs : List ℕ) {z : ℕ} →
          z ∈ minus cs bs → (z ∈ cs) × (∀ {y : ℕ} → y ∈ bs → z ≢ y)
minus-∈ cs []       mem = mem , none
  where
  none : ∀ {y : ℕ} → y ∈ [] → _
  none ()
minus-∈ cs (b ∷ bs) {z} mem = proj₁ head , off
  where
  rec : (z ∈ flt b cs) × (∀ {y : ℕ} → y ∈ bs → z ≢ y)
  rec = minus-∈ (flt b cs) bs mem

  head : (z ∈ cs) × (z ≢ b)
  head = flt-∈ b cs (proj₁ rec)

  off : ∀ {y : ℕ} → y ∈ (b ∷ bs) → z ≢ y
  off here      = proj₂ head
  off (there t) = proj₂ rec t

minus-Up : ∀ {n : ℕ} (cs bs : List ℕ) → Up n cs → Up n (minus cs bs)
minus-Up cs []       up = up
minus-Up cs (b ∷ bs) up = minus-Up (flt b cs) bs (flt-Up b cs up)

minus-len : ∀ {n : ℕ} (cs bs : List ℕ) → Up n cs →
            length cs ≤ length (minus cs bs) + length bs
minus-len cs []       up = ≤-reflexive (Eq.sym (+-identityʳ (length cs)))
minus-len cs (b ∷ bs) up =
  ≤-trans (flt-len b cs up)
          (≤-trans (s≤s (minus-len (flt b cs) bs (flt-Up b cs up)))
                   (≤-reflexive (Eq.sym (+-suc _ (length bs)))))

------------------------------------------------------------------------
-- The eight numerals every width has

cand : List ℕ
cand = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []

cand-Up : Up 0 cand
cand-Up = cons z≤n (cons ≤-refl (cons ≤-refl (cons ≤-refl (cons ≤-refl
            (cons ≤-refl (cons ≤-refl (cons ≤-refl nil)))))))

cand-< : ∀ {z : ℕ} → z ∈ cand → z < 8
cand-< here                                         = s≤s z≤n
cand-< (there here)                                 = s≤s (s≤s z≤n)
cand-< (there (there here))                         = s≤s (s≤s (s≤s z≤n))
cand-< (there (there (there here)))                 =
  s≤s (s≤s (s≤s (s≤s z≤n)))
cand-< (there (there (there (there here))))         =
  s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
cand-< (there (there (there (there (there here))))) =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
cand-< (there (there (there (there (there (there here)))))) =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
cand-< (there (there (there (there (there (there (there here))))))) =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

------------------------------------------------------------------------
-- Two survivors

record Two (bs : List ℕ) : Set where
  field
    p q : ℕ
    p<  : p < 8
    q<  : q < 8
    p≢q : p ≢ q
    p∉  : ∀ {y : ℕ} → y ∈ bs → p ≢ y
    q∉  : ∀ {y : ℕ} → y ∈ bs → q ≢ y

private
  no8 : ∀ {A : Set} → 8 ≤ 7 → A
  no8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))

  4≤7 : 4 ≤ 7
  4≤7 = s≤s (s≤s (s≤s (s≤s z≤n)))

-- Six blocked values leave two of the eight numerals free.
avoid : ∀ (bs : List ℕ) → length bs ≤ 6 → Two bs
avoid bs le6 =
  go (minus cand bs) (minus-len cand bs cand-Up) (minus-Up cand bs cand-Up)
     (minus-∈ cand bs)
  where
  go : ∀ (r : List ℕ) → 8 ≤ length r + length bs → Up 0 r →
       (∀ {z : ℕ} → z ∈ r → (z ∈ cand) × (∀ {y : ℕ} → y ∈ bs → z ≢ y)) →
       Two bs
  go []          le up f = no8 (≤-trans le (m≤n⇒m≤1+n le6))
  go (x ∷ [])    le up f = no8 (≤-trans le (s≤s le6))
  go (x ∷ y ∷ r) le (cons _ (cons xy up)) f =
    record { p = x ; q = y
           ; p< = cand-< (proj₁ (f here))
           ; q< = cand-< (proj₁ (f (there here)))
           ; p≢q = <⇒≢ xy
           ; p∉ = proj₂ (f here)
           ; q∉ = proj₂ (f (there here)) }

------------------------------------------------------------------------
-- Four blocked values leave two of the numerals in reach of `twoSmallest`
--
-- Equation (42) splits a Hadamard letter over the two smallest
-- naturals its four indices miss, and `Small` has to know those two
-- are below eight.  Deleting four values from 0 … 7 leaves four, so
-- the first of the survivors is at most 4 and the second at most 5 —
-- which is where a search from 0 with fuel 5 can reach.

record Four (bs : List ℕ) : Set where
  field
    h₀ h₁ : ℕ
    h₀≤4  : h₀ ≤ 4
    h₁≤5  : h₁ ≤ 5
    h₀<h₁ : h₀ < h₁
    h₀∉   : ∀ {y : ℕ} → y ∈ bs → h₀ ≢ y
    h₁∉   : ∀ {y : ℕ} → y ∈ bs → h₁ ≢ y

avoid4 : ∀ (bs : List ℕ) → length bs ≤ 4 → Four bs
avoid4 bs le4 =
  go (minus cand bs) (minus-len cand bs cand-Up) (minus-Up cand bs cand-Up)
     (minus-∈ cand bs)
  where
  go : ∀ (r : List ℕ) → 8 ≤ length r + length bs → Up 0 r →
       (∀ {z : ℕ} → z ∈ r → (z ∈ cand) × (∀ {y : ℕ} → y ∈ bs → z ≢ y)) →
       Four bs
  go []                  le up f = no8 (≤-trans le (≤-trans le4 4≤7))
  go (_ ∷ [])            le up f = no8 (≤-trans le (s≤s (≤-trans le4 (m≤n⇒m≤1+n
                                     (m≤n⇒m≤1+n ≤-refl)))))
  go (_ ∷ _ ∷ [])        le up f = no8 (≤-trans le (s≤s (s≤s (≤-trans le4
                                     (m≤n⇒m≤1+n ≤-refl)))))
  go (_ ∷ _ ∷ _ ∷ [])    le up f = no8 (≤-trans le (s≤s (s≤s (s≤s le4))))
  go (x ∷ y ∷ z ∷ w ∷ r) le (cons _ (cons xy (cons yz (cons zw up)))) f =
    record { h₀ = x ; h₁ = y
           ; h₀≤4 = ≤-pred (≤-pred (≤-pred (≤-trans d₃ w≤7)))
           ; h₁≤5 = ≤-pred (≤-pred (≤-trans d₂ w≤7))
           ; h₀<h₁ = xy
           ; h₀∉ = proj₂ (f here)
           ; h₁∉ = proj₂ (f (there here)) }
    where
    w≤7 : w ≤ 7
    w≤7 = ≤-pred (cand-< (proj₁ (f (there (there (there here))))))

    d₂ : suc (suc y) ≤ w
    d₂ = ≤-trans (s≤s yz) zw

    d₃ : suc (suc (suc x)) ≤ w
    d₃ = ≤-trans (s≤s (s≤s xy)) d₂

------------------------------------------------------------------------
-- Five blocked values leave three
--
-- What `Frame` needs: a sign sink and a Hadamard pair away from the
-- two distinguished indices and the at most three indices of a rule.

record Three (bs : List ℕ) : Set where
  field
    p q r : ℕ
    p<    : p < 8
    q<    : q < 8
    r<    : r < 8
    p≢q   : p ≢ q
    p≢r   : p ≢ r
    q≢r   : q ≢ r
    p∉    : ∀ {y : ℕ} → y ∈ bs → p ≢ y
    q∉    : ∀ {y : ℕ} → y ∈ bs → q ≢ y
    r∉    : ∀ {y : ℕ} → y ∈ bs → r ≢ y

avoid3 : ∀ (bs : List ℕ) → length bs ≤ 5 → Three bs
avoid3 bs le5 =
  go (minus cand bs) (minus-len cand bs cand-Up) (minus-Up cand bs cand-Up)
     (minus-∈ cand bs)
  where
  go : ∀ (r : List ℕ) → 8 ≤ length r + length bs → Up 0 r →
       (∀ {z : ℕ} → z ∈ r → (z ∈ cand) × (∀ {y : ℕ} → y ∈ bs → z ≢ y)) →
       Three bs
  go []               le up f = no8 (≤-trans le (m≤n⇒m≤1+n (m≤n⇒m≤1+n le5)))
  go (_ ∷ [])         le up f = no8 (≤-trans le (s≤s (m≤n⇒m≤1+n le5)))
  go (_ ∷ _ ∷ [])     le up f = no8 (≤-trans le (s≤s (s≤s le5)))
  go (x ∷ y ∷ w ∷ rs) le (cons _ (cons xy (cons yw up))) f =
    record { p = x ; q = y ; r = w
           ; p< = cand-< (proj₁ (f here))
           ; q< = cand-< (proj₁ (f (there here)))
           ; r< = cand-< (proj₁ (f (there (there here))))
           ; p≢q = <⇒≢ xy
           ; p≢r = <⇒≢ (<-trans xy yw)
           ; q≢r = <⇒≢ yw
           ; p∉ = proj₂ (f here)
           ; q∉ = proj₂ (f (there here))
           ; r∉ = proj₂ (f (there (there here))) }
