------------------------------------------------------------------------
-- Presentations of groups
--
-- Fresh indices
--
-- The coset action spells K_[d,e] i_[0]⁻¹ — which has determinant 1
-- but is no letter — through a K pair and a phase pair on indices
-- away from 0, d and e: on four indices no such word exists
-- (scratchpad/four-wire-notes.md), so fresh ones are part of the
-- definition.  Every real width has at least sixteen indices, and a
-- handful of blocked values leaves enough of the numerals 0 … 15
-- free.
--
-- They are found as Real-Clifford+CH's `Avoid` finds its numerals, by
-- deletion: delete each blocked value from 0 … 15 in turn, and read
-- the first survivors off.  The survivors increase strictly and avoid
-- every blocked value by construction, and deleting one value
-- shortens the list by at most one, which is the whole of the
-- counting.  Here the survivors are then read as indices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.Fresh (N : ℕ) (big : 16 ≤ N) where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (_<_ to _<ᶠ_)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.List using (List ; [] ; _∷_ ; length ; map)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat using (zero ; suc ; _+_ ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; ≤-reflexive ; n≮n ; +-monoʳ-≤ ; m≤m+n)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Avoid
  using (_∈_ ; here ; there ; Up ; nil ; cons ; minus ; minus-∈ ; minus-Up
       ; minus-len)

------------------------------------------------------------------------
-- The numerals 0 … 15

private
  from : ℕ → ℕ → List ℕ
  from s zero    = []
  from s (suc k) = s ∷ from (suc s) k

  from-Up : ∀ (s k : ℕ) → Up s (from s k)
  from-Up s zero    = nil
  from-Up s (suc k) = cons ≤-refl (from-Up (suc s) k)

  from-< : ∀ (s k : ℕ) {z : ℕ} → z ∈ from s k → z < s + k
  from-< s (suc k) here = go s k
    where
    go : ∀ s k → s < s + suc k
    go zero    k = s≤s z≤n
    go (suc s) k = s≤s (go s k)
  from-< s (suc k) {z} (there mem) =
    Eq.subst (z <_) (+suc s k) (from-< (suc s) k mem)
    where
    +suc : ∀ s k → suc s + k ≡ s + suc k
    +suc zero    k = Eq.refl
    +suc (suc s) k = Eq.cong suc (+suc s k)

  cand : List ℕ
  cand = from 0 16

  cand-< : ∀ {z : ℕ} → z ∈ cand → z < 16
  cand-< = from-< 0 16

------------------------------------------------------------------------
-- From numerals to indices

private
  fin : ∀ (z : ℕ) → z < 16 → Fin N
  fin z lt = fromℕ< (≤-trans lt big)

  toℕ-fin : ∀ (z : ℕ) (lt : z < 16) → toℕ (fin z lt) ≡ z
  toℕ-fin z lt = toℕ-fromℕ< (≤-trans lt big)

  fin-< : ∀ {x y : ℕ} (px : x < 16) (py : y < 16) → x < y →
          fin x px <ᶠ fin y py
  fin-< {x} {y} px py lt =
    Eq.subst₂ _<_ (Eq.sym (toℕ-fin x px)) (Eq.sym (toℕ-fin y py)) lt

-- An index off a list: different from each of its entries.
Off : List (Fin N) → Fin N → Set
Off bs x = All (λ y → x ≢ y) bs

private
  -- A numeral off the numerals of a list gives an index off the list.
  off : ∀ (bs : List (Fin N)) {z : ℕ} (lt : z < 16) →
        (∀ {y : ℕ} → y ∈ map toℕ bs → z ≢ y) → Off bs (fin z lt)
  off []       lt f = []
  off (b ∷ bs) {z} lt f =
    (λ e → f here (Eq.trans (Eq.sym (toℕ-fin z lt)) (Eq.cong toℕ e)))
    ∷ off bs lt (λ mem → f (there mem))

------------------------------------------------------------------------
-- Three and four fresh indices

record Fresh3 (bs : List (Fin N)) : Set where
  field
    f₁ f₂ f₃ : Fin N
    f₁<f₂    : f₁ <ᶠ f₂
    f₂<f₃    : f₂ <ᶠ f₃
    off₁     : Off bs f₁
    off₂     : Off bs f₂
    off₃     : Off bs f₃

record Fresh4 (bs : List (Fin N)) : Set where
  field
    f₁ f₂ f₃ f₄ : Fin N
    f₁<f₂       : f₁ <ᶠ f₂
    f₂<f₃       : f₂ <ᶠ f₃
    f₃<f₄       : f₃ <ᶠ f₄
    off₁        : Off bs f₁
    off₂        : Off bs f₂
    off₃        : Off bs f₃
    off₄        : Off bs f₄

private
  Surv : List ℕ → List ℕ → Set
  Surv ns r = ∀ {z : ℕ} → z ∈ r → (z ∈ cand) × (∀ {y : ℕ} → y ∈ ns → z ≢ y)

  -- Too few survivors contradict the count.
  short : ∀ {k b l : ℕ} → k + b ≤ 15 → l ≤ b → 16 ≤ k + l → ⊥
  short {k} bound lb le = n≮n 15 (≤-trans le (≤-trans (+-monoʳ-≤ k lb) bound))

-- Thirteen blocked values leave three.
fresh3 : ∀ (bs : List (Fin N)) → length bs ≤ 13 → Fresh3 bs
fresh3 bs le =
  go (minus cand ns) (minus-len cand ns (from-Up 0 16))
     (minus-Up cand ns (from-Up 0 16)) (minus-∈ cand ns)
  where
  ns : List ℕ
  ns = map toℕ bs

  lb : length ns ≤ 13
  lb = ≤-trans (≤-reflexive (length-map toℕ bs)) le

  go : ∀ (r : List ℕ) → 16 ≤ length r + length ns → Up 0 r → Surv ns r →
       Fresh3 bs
  go []           l up f = ⊥-elim (short {0} (m≤m+n 13 2) lb l)
  go (_ ∷ [])     l up f = ⊥-elim (short {1} (m≤m+n 14 1) lb l)
  go (_ ∷ _ ∷ []) l up f = ⊥-elim (short {2} ≤-refl lb l)
  go (x ∷ y ∷ z ∷ r) l (cons _ (cons xy (cons yz _))) f =
    record { f₁ = fin x px ; f₂ = fin y py ; f₃ = fin z pz
           ; f₁<f₂ = fin-< px py xy
           ; f₂<f₃ = fin-< py pz yz
           ; off₁ = off bs px (proj₂ (f here))
           ; off₂ = off bs py (proj₂ (f (there here)))
           ; off₃ = off bs pz (proj₂ (f (there (there here)))) }
    where
    px = cand-< (proj₁ (f here))
    py = cand-< (proj₁ (f (there here)))
    pz = cand-< (proj₁ (f (there (there here))))

-- Twelve blocked values leave four.
fresh4 : ∀ (bs : List (Fin N)) → length bs ≤ 12 → Fresh4 bs
fresh4 bs le =
  go (minus cand ns) (minus-len cand ns (from-Up 0 16))
     (minus-Up cand ns (from-Up 0 16)) (minus-∈ cand ns)
  where
  ns : List ℕ
  ns = map toℕ bs

  lb : length ns ≤ 12
  lb = ≤-trans (≤-reflexive (length-map toℕ bs)) le

  go : ∀ (r : List ℕ) → 16 ≤ length r + length ns → Up 0 r → Surv ns r →
       Fresh4 bs
  go []               l up f = ⊥-elim (short {0} (m≤m+n 12 3) lb l)
  go (_ ∷ [])         l up f = ⊥-elim (short {1} (m≤m+n 13 2) lb l)
  go (_ ∷ _ ∷ [])     l up f = ⊥-elim (short {2} (m≤m+n 14 1) lb l)
  go (_ ∷ _ ∷ _ ∷ []) l up f = ⊥-elim (short {3} ≤-refl lb l)
  go (x ∷ y ∷ z ∷ w ∷ r) l (cons _ (cons xy (cons yz (cons zw _)))) f =
    record { f₁ = fin x px ; f₂ = fin y py ; f₃ = fin z pz ; f₄ = fin w pw
           ; f₁<f₂ = fin-< px py xy
           ; f₂<f₃ = fin-< py pz yz
           ; f₃<f₄ = fin-< pz pw zw
           ; off₁ = off bs px (proj₂ (f here))
           ; off₂ = off bs py (proj₂ (f (there here)))
           ; off₃ = off bs pz (proj₂ (f (there (there here))))
           ; off₄ = off bs pw (proj₂ (f (there (there (there here))))) }
    where
    px = cand-< (proj₁ (f here))
    py = cand-< (proj₁ (f (there here)))
    pz = cand-< (proj₁ (f (there (there here))))
    pw = cand-< (proj₁ (f (there (there (there here)))))
