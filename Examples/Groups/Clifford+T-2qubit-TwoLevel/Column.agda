------------------------------------------------------------------------
-- Presentations of groups
--
-- The syllables of the exact synthesis algorithm (Algorithm 2.14), as
-- a function of the data of the pivot column: its index p, its least
-- δ-exponent k and its numerator w ∈ ℤ[ω]ⁿ.
--
-- * k = 0: w has a single nonzero entry, a unit u = ωᵗ at index m
--   (Lemma 2.12), and the syllable is ω_[m]ᵉ followed by X_[m,p]
--   (if m < p), where ωᵉ u = 1;
-- * k > 0: with j < ℓ the first two odd entries of w (Lemma 2.13) and
--   z < 4 such that ωᶻ w_j ≡ w_ℓ (mod δ³) (Lemma 2.11), the syllable
--   is ω_[j]ᶻ followed by H_[j,ℓ] (Lemma 2.12).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Column where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-yes ; dec-no ; dec-true ; dec-false)

open import Quantum.Synthesis.Ring using (Omega)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue public using (zOf ; zOf-spec ; zOf-<)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde using (_!_ ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Odd entries

-- The number of odd entries.
nodd : Vec Z n → ℕ
nodd w = count (λ x → oddᶻ (w ! x))

-- The first odd entry.
firstOdd : Vec Z n → Maybe (Fin n)
firstOdd w = first (λ x → oddᶻ (w ! x))

-- The first odd entry after j.
nextOdd : Fin n → Vec Z n → Maybe (Fin n)
nextOdd j w = first (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x))

------------------------------------------------------------------------
-- Units and the exponent that normalises them

-- invExp u = e with ωᵉ u = 1, for u a power of ω.
invExp : Z → ℕ
invExp (Omega (+ 0) (+ 0) (+ 0) (+ 1)) = 0
invExp (Omega (+ 0) (+ 0) (+ 1) (+ 0)) = 7
invExp (Omega (+ 0) (+ 1) (+ 0) (+ 0)) = 6
invExp (Omega (+ 1) (+ 0) (+ 0) (+ 0)) = 5
invExp (Omega (+ 0) (+ 0) (+ 0) -[1+ 0 ]) = 4
invExp (Omega (+ 0) (+ 0) -[1+ 0 ] (+ 0)) = 3
invExp (Omega (+ 0) -[1+ 0 ] (+ 0) (+ 0)) = 2
invExp (Omega -[1+ 0 ] (+ 0) (+ 0) (+ 0)) = 1
invExp _ = 0

private
  -- t < 8 enumerated.
  lt8 : ∀ {P : ℕ → Set} → P 0 → P 1 → P 2 → P 3 → P 4 → P 5 → P 6 → P 7 → ∀ t → t ℕ.< 8 → P t
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 0 _ = p0
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 1 _ = p1
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 2 _ = p2
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 3 _ = p3
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 4 _ = p4
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 5 _ = p5
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 6 _ = p6
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 7 _ = p7
  lt8 p0 p1 p2 p3 p4 p5 p6 p7 (suc (suc (suc (suc (suc (suc (suc (suc t)))))))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ()))))))))

invExp-unit : ∀ t → t ℕ.< 8 → (ωᶻ ^ᶻ invExp (ωᶻ ^ᶻ t)) ZR.* (ωᶻ ^ᶻ t) ≡ ZR.1#
invExp-unit = lt8 {λ t → (ωᶻ ^ᶻ invExp (ωᶻ ^ᶻ t)) ZR.* (ωᶻ ^ᶻ t) ≡ ZR.1#} refl refl refl refl refl refl refl refl

invExp-< : ∀ t → t ℕ.< 8 → invExp (ωᶻ ^ᶻ t) ℕ.< 8
invExp-< = lt8 {λ t → invExp (ωᶻ ^ᶻ t) ℕ.< 8}
  (ℕP.<ᵇ⇒< 0 8 _) (ℕP.<ᵇ⇒< 7 8 _) (ℕP.<ᵇ⇒< 6 8 _) (ℕP.<ᵇ⇒< 5 8 _)
  (ℕP.<ᵇ⇒< 4 8 _) (ℕP.<ᵇ⇒< 3 8 _) (ℕP.<ᵇ⇒< 2 8 _) (ℕP.<ᵇ⇒< 1 8 _)

-- The only unit u with invExp u = 0 is 1.
invExp-0 : ∀ t → t ℕ.< 8 → invExp (ωᶻ ^ᶻ t) ≡ 0 → ωᶻ ^ᶻ t ≡ ZR.1#
invExp-0 = lt8 {λ t → invExp (ωᶻ ^ᶻ t) ≡ 0 → ωᶻ ^ᶻ t ≡ ZR.1#}
  (λ _ → refl) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- Units are odd.
unit-odd : ∀ t → t ℕ.< 8 → Odd (ωᶻ ^ᶻ t)
unit-odd = lt8 {λ t → Odd (ωᶻ ^ᶻ t)} refl refl refl refl refl refl refl refl
------------------------------------------------------------------------
-- The syllable of a pivot column

-- k = 0: the unit at index m (if found), with invExp e.
unitSyl : (p m : Fin n) → ℕ → Dec (m < p) → Word (Gen n)
unitSyl p m e (yes m<p) = X m p m<p • ω m ^ e
unitSyl p m e (no  _)   = ω p ^ e

-- k > 0: the first two odd entries j < ℓ.
pairSyl : (w : Vec Z n) (j ℓ : Fin n) → Dec (j < ℓ) → Word (Gen n)
pairSyl w j ℓ (yes j<ℓ) = H j ℓ j<ℓ • ω j ^ zOf (w ! j) (w ! ℓ)
pairSyl w j ℓ (no  _)   = ε

private
  unitStep : Fin n → Vec Z n → Maybe (Fin n) → Word (Gen n)
  unitStep p w (just m) = unitSyl p m (invExp (w ! m)) (m FinP.<? p)
  unitStep p w nothing  = ε

  pairStep₂ : Vec Z n → Fin n → Maybe (Fin n) → Word (Gen n)
  pairStep₂ w j (just ℓ) = pairSyl w j ℓ (j FinP.<? ℓ)
  pairStep₂ w j nothing  = ε

  pairStep : Vec Z n → Maybe (Fin n) → Word (Gen n)
  pairStep w (just j) = pairStep₂ w j (nextOdd j w)
  pairStep w nothing  = ε

sylData : Fin n → ℕ → Vec Z n → Word (Gen n)
sylData p zero    w = unitStep p w (firstOdd w)
sylData p (suc k) w = pairStep w (firstOdd w)

-- The syllable, from the facts that determine it.
sylData-unit< : ∀ {p m : Fin n} (w : Vec Z n) → firstOdd w ≡ just m → (m<p : m < p) →
                sylData p 0 w ≡ X m p m<p • ω m ^ invExp (w ! m)
sylData-unit< {p = p} {m} w fo m<p rewrite fo with m FinP.<? p
... | yes _ = refl
... | no ¬m<p = ⊥-elim (¬m<p m<p)

sylData-unit≡ : ∀ {p : Fin n} (w : Vec Z n) → firstOdd w ≡ just p →
                sylData p 0 w ≡ ω p ^ invExp (w ! p)
sylData-unit≡ {p = p} w fo rewrite fo with p FinP.<? p
... | yes p<p = ⊥-elim (FinP.<-irrefl refl p<p)
... | no _ = refl

sylData-pair : ∀ {p j ℓ : Fin n} k (w : Vec Z n) → firstOdd w ≡ just j → nextOdd j w ≡ just ℓ →
               (j<ℓ : j < ℓ) → sylData p (suc k) w ≡ H j ℓ j<ℓ • ω j ^ zOf (w ! j) (w ! ℓ)
sylData-pair {j = j} {ℓ} k w fo nx j<ℓ rewrite fo | nx with j FinP.<? ℓ
... | yes _ = refl
... | no ¬j<ℓ = ⊥-elim (¬j<ℓ j<ℓ)

------------------------------------------------------------------------
-- Characterising the first odd entries

firstOdd-char : ∀ (w : Vec Z n) {j} → Odd (w ! j) → (∀ x → x < j → Even (w ! x)) → firstOdd w ≡ just j
firstOdd-char w oj below = first-char (λ x → oddᶻ (w ! x)) oj below

nextOdd-char : ∀ (w : Vec Z n) {j ℓ} → j < ℓ → Odd (w ! ℓ) →
               (∀ x → j < x → x < ℓ → Even (w ! x)) → nextOdd j w ≡ just ℓ
nextOdd-char w {j} {ℓ} j<ℓ oℓ between =
  first-char (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x))
    (trans (cong (_∧ oddᶻ (w ! ℓ)) (dec-true (j FinP.<? ℓ) j<ℓ)) oℓ) below
  where
  below : ∀ x → x < ℓ → does (j FinP.<? x) ∧ oddᶻ (w ! x) ≡ false
  below x x<ℓ = aux (j FinP.<? x)
    where
    aux : (d : Dec (j < x)) → does d ∧ oddᶻ (w ! x) ≡ false
    aux (yes j<x) = between x j<x x<ℓ
    aux (no  _)   = refl

firstOdd-spec : ∀ (w : Vec Z n) {j} → firstOdd w ≡ just j → Odd (w ! j) × (∀ x → x < j → Even (w ! x))
firstOdd-spec w eq = first-just (λ x → oddᶻ (w ! x)) eq

firstOdd-nothing : ∀ (w : Vec Z n) → firstOdd w ≡ nothing → ∀ x → Even (w ! x)
firstOdd-nothing w eq = first-nothing (λ x → oddᶻ (w ! x)) eq

nextOdd-spec : ∀ (w : Vec Z n) {j ℓ} → nextOdd j w ≡ just ℓ →
               j < ℓ × Odd (w ! ℓ) × (∀ x → j < x → x < ℓ → Even (w ! x))
nextOdd-spec w {j} {ℓ} eq with first-just (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x)) eq
... | Pℓ , below = proj₁ (split ℓ (j FinP.<? ℓ) Pℓ) , proj₂ (split ℓ (j FinP.<? ℓ) Pℓ) , between
  where
  split : ∀ x (d : Dec (j < x)) → does d ∧ oddᶻ (w ! x) ≡ true → j < x × Odd (w ! x)
  split x (yes j<x) P = j<x , P
  split x (no  _)   ()
  between : ∀ x → j < x → x < ℓ → Even (w ! x)
  between x j<x x<ℓ = aux (j FinP.<? x) (below x x<ℓ)
    where
    aux : (d : Dec (j < x)) → does d ∧ oddᶻ (w ! x) ≡ false → Even (w ! x)
    aux (yes _) e = e
    aux (no ¬j<x) _ = ⊥-elim (¬j<x j<x)

------------------------------------------------------------------------
-- The syllable depends only on the parities and the odd entries

firstOdd-cong : (w w′ : Vec Z n) → (∀ x → oddᶻ (w ! x) ≡ oddᶻ (w′ ! x)) → firstOdd w ≡ firstOdd w′
firstOdd-cong w w′ par = first-cong (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (w′ ! x)) par

nextOdd-cong : (j : Fin n) (w w′ : Vec Z n) → (∀ x → oddᶻ (w ! x) ≡ oddᶻ (w′ ! x)) → nextOdd j w ≡ nextOdd j w′
nextOdd-cong j w w′ par =
  first-cong (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x)) (λ x → does (j FinP.<? x) ∧ oddᶻ (w′ ! x))
             (λ x → cong (does (j FinP.<? x) ∧_) (par x))

sylData-agree : (p : Fin n) (k : ℕ) (w w′ : Vec Z n) →
                (∀ x → oddᶻ (w ! x) ≡ oddᶻ (w′ ! x)) → (∀ x → Odd (w ! x) → w ! x ≡ w′ ! x) →
                sylData p k w ≡ sylData p k w′
sylData-agree p zero w w′ par agree =
  trans (unit (firstOdd w) refl) (cong (unitStep p w′) (firstOdd-cong w w′ par))
  where
  unit : (r : Maybe (Fin _)) → firstOdd w ≡ r → unitStep p w r ≡ unitStep p w′ r
  unit nothing _ = refl
  unit (just m) e = cong (λ z → unitSyl p m (invExp z) (m FinP.<? p)) (agree m (proj₁ (firstOdd-spec w e)))
sylData-agree p (suc k) w w′ par agree =
  trans (pair (firstOdd w) refl) (cong (pairStep w′) (firstOdd-cong w w′ par))
  where
  syl-agree : ∀ j ℓ → w ! j ≡ w′ ! j → w ! ℓ ≡ w′ ! ℓ → (d : Dec (j < ℓ)) → pairSyl w j ℓ d ≡ pairSyl w′ j ℓ d
  syl-agree j ℓ ej eℓ (yes j<ℓ) = cong₂ (λ a b → H j ℓ j<ℓ • ω j ^ zOf a b) ej eℓ
  syl-agree j ℓ ej eℓ (no _) = refl
  pair : (r : Maybe (Fin _)) → firstOdd w ≡ r → pairStep w r ≡ pairStep w′ r
  pair nothing _ = refl
  pair (just j) e = trans (two (nextOdd j w) refl) (cong (pairStep₂ w′ j) (nextOdd-cong j w w′ par))
    where
    oj : Odd (w ! j)
    oj = proj₁ (firstOdd-spec w e)
    two : (r : Maybe (Fin _)) → nextOdd j w ≡ r → pairStep₂ w j r ≡ pairStep₂ w′ j r
    two nothing _ = refl
    two (just ℓ) e′ = syl-agree j ℓ (agree j oj) (agree ℓ (proj₁ (proj₂ (nextOdd-spec w e′)))) (j FinP.<? ℓ)

------------------------------------------------------------------------
-- The syllable acts at or above the first odd entry

-- Every letter acts on indices ≥ j.
Above : Fin n → Word (Gen n) → Set
Above j [ X-gen a b _ ]ʷ = j Fin.≤ a
Above j [ H-gen a b _ ]ʷ = j Fin.≤ a
Above j [ ω-gen a ]ʷ = j Fin.≤ a
Above j ε = ⊤
Above j (u • v) = Above j u × Above j v

Above-^ : ∀ {j : Fin n} (w : Word (Gen n)) → Above j w → ∀ e → Above j (w ^ e)
Above-^ w h zero = tt
Above-^ w h (suc zero) = h
Above-^ w h (suc (suc e)) = h , Above-^ w h (suc e)

sylData-above : (p : Fin n) (k : ℕ) (w : Vec Z n) {j : Fin n} → firstOdd w ≡ just j → j Fin.≤ p →
                Above j (sylData p k w)
sylData-above p zero w {j} fo j≤p = subst (λ r → Above j (unitStep p w r)) (sym fo) (unit (j FinP.<? p))
  where
  unit : (d : Dec (j < p)) → Above j (unitSyl p j (invExp (w ! j)) d)
  unit (yes j<p) = FinP.≤-refl , Above-^ (ω j) FinP.≤-refl (invExp (w ! j))
  unit (no ¬j<p) = Above-^ (ω p) j≤p (invExp (w ! j))
sylData-above p (suc k) w {j} fo j≤p = subst (λ r → Above j (pairStep w r)) (sym fo) (two (nextOdd j w) refl)
  where
  two : (r : Maybe (Fin _)) → nextOdd j w ≡ r → Above j (pairStep₂ w j r)
  two nothing _ = tt
  two (just ℓ) e = syl (j FinP.<? ℓ)
    where
    syl : (d : Dec (j < ℓ)) → Above j (pairSyl w j ℓ d)
    syl (yes j<ℓ) = FinP.≤-refl , Above-^ (ω j) FinP.≤-refl (zOf (w ! j) (w ! ℓ))
    syl (no _) = tt
