------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemmas for the block normal form: subsets, their partition lists,
-- and signs
--
-- A subset S of n states (a predicate) gives the list of its states in
-- order followed by the others (ts S, from part).  That list is
-- distinct (ts-distinct) and the decision procedure distinct? finds it
-- so (distinct?-complete); its k-th entry is in S exactly when k is
-- below the size of S (‼-ts); and the size of a subset is invariant
-- under a permutation of the states (weight-perm).  Signs: a lifted
-- permutation and a conjugate have the sign of the permutation
-- (sign-liftN, sign-conj); these are stated at a variable width, where
-- comparing two spellings of a sign cannot set off an evaluation of
-- Symmetric's word for the permutation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.NFLib where

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Bool.Properties using (xor-assoc ; xor-comm)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Fin.Permutation using (Permutation′ ; _⟨$⟩ʳ_ ; _∘ₚ_ ; flip)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; length)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _<ᵇ_ ; _≤_ ; _<_ ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable.Core using (Dec ; yes ; no)
open import Data.Empty using (⊥-elim)
open import Word.Base using (Word ; ε)
import Examples.Groups.Symmetric.Interpretation as SymI
open import Data.Fin.Permutation using (_⟨$⟩ˡ_)

import Algebra.Properties.CommutativeMonoid.Sum as Sum

import Examples.Groups.Symmetric.CoxeterFrames as CF
open CF using (Avoid ; Distinct ; _‼_ ; liftN ; SG ; actₙ ; frame ; frame-act)
open import Examples.Groups.Alternating.Parity using (sign ; sign-lift₀ ; sign-∘ ; sign-cong)

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- The partition list of a subset

-- The states of S in order, and the others in order.
step : Bool → List (Fin n) × List (Fin n) → List (Fin (suc n)) × List (Fin (suc n))
step true  (a , b) = zero ∷ map suc a , map suc b
step false (a , b) = map suc a , zero ∷ map suc b

part : (Fin n → Bool) → List (Fin n) × List (Fin n)
part {zero}  S = [] , []
part {suc n} S = step (S zero) (part (λ i → S (suc i)))

ts : (Fin n → Bool) → List (Fin n)
ts S = proj₁ (part S) ++ proj₂ (part S)

-- The number of states of S.
weight : (Fin n → Bool) → ℕ
weight S = length (proj₁ (part S))

part-cong : {S S′ : Fin n → Bool} → (∀ i → S i ≡ S′ i) → part S ≡ part S′
part-cong {zero}  e = Eq.refl
part-cong {suc n} {S} {S′} e =
  Eq.cong₂ step (e zero) (part-cong {n} {λ i → S (suc i)} {λ i → S′ (suc i)} (λ i → e (suc i)))

ts-cong : {S S′ : Fin n → Bool} → (∀ i → S i ≡ S′ i) → ts S ≡ ts S′
ts-cong e = Eq.cong (λ p → proj₁ p ++ proj₂ p) (part-cong e)

private
  length-map : {A B : Set} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
  length-map f []       = Eq.refl
  length-map f (x ∷ xs) = Eq.cong suc (length-map f xs)

  length-++ : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       ys = Eq.refl
  length-++ (x ∷ xs) ys = Eq.cong suc (length-++ xs ys)

  step-length : (b : Bool) (p : List (Fin n) × List (Fin n)) →
                length (proj₁ (step b p)) + length (proj₂ (step b p)) ≡ suc (length (proj₁ p) + length (proj₂ p))
  step-length true  (a , b) = Eq.cong suc (Eq.cong₂ _+_ (length-map suc a) (length-map suc b))
  step-length false (a , b) =
    Eq.trans (Eq.cong₂ _+_ (length-map suc a) (Eq.cong suc (length-map suc b))) (ℕP.+-suc (length a) (length b))

part-length : (S : Fin n → Bool) → length (proj₁ (part S)) + length (proj₂ (part S)) ≡ n
part-length {zero}  S = Eq.refl
part-length {suc n} S =
  Eq.trans (step-length (S zero) (part (λ i → S (suc i)))) (Eq.cong suc (part-length (λ i → S (suc i))))

ts-length : (S : Fin n → Bool) → length (ts S) ≡ n
ts-length S = Eq.trans (length-++ (proj₁ (part S)) (proj₂ (part S))) (part-length S)

------------------------------------------------------------------------
-- Entries of the lists

private
  ‼-map : {A B : Set} (f : A → B) (xs : List A) (k : ℕ) {y : B} → map f xs ‼ k ≡ just y →
          Σ A (λ x → (xs ‼ k ≡ just x) × (f x ≡ y))
  ‼-map f (x ∷ xs) zero    Eq.refl = x , Eq.refl , Eq.refl
  ‼-map f (x ∷ xs) (suc k) h       = ‼-map f xs k h

-- An entry of the first list is in S, of the second is not.
‼-in₁ : (S : Fin n → Bool) (k : ℕ) {x : Fin n} → proj₁ (part S) ‼ k ≡ just x → S x ≡ true
‼-in₂ : (S : Fin n → Bool) (k : ℕ) {x : Fin n} → proj₂ (part S) ‼ k ≡ just x → S x ≡ false

‼-in₁ {suc n} S k h = go (S zero) Eq.refl (part (λ i → S (suc i))) Eq.refl k h
  where
  go : (b : Bool) → S zero ≡ b → (p : List (Fin n) × List (Fin n)) → part (λ i → S (suc i)) ≡ p →
       (k : ℕ) {x : Fin (suc n)} → proj₁ (step b p) ‼ k ≡ just x → S x ≡ true
  go true  e (a , c) q zero    Eq.refl = e
  go true  e (a , c) q (suc k) h with ‼-map suc a k h
  ... | y , hy , Eq.refl = ‼-in₁ (λ i → S (suc i)) k (Eq.subst (λ p → proj₁ p ‼ k ≡ just y) (Eq.sym q) hy)
  go false e (a , c) q k h with ‼-map suc a k h
  ... | y , hy , Eq.refl = ‼-in₁ (λ i → S (suc i)) k (Eq.subst (λ p → proj₁ p ‼ k ≡ just y) (Eq.sym q) hy)

‼-in₂ {suc n} S k h = go (S zero) Eq.refl (part (λ i → S (suc i))) Eq.refl k h
  where
  go : (b : Bool) → S zero ≡ b → (p : List (Fin n) × List (Fin n)) → part (λ i → S (suc i)) ≡ p →
       (k : ℕ) {x : Fin (suc n)} → proj₂ (step b p) ‼ k ≡ just x → S x ≡ false
  go false e (a , c) q zero    Eq.refl = e
  go false e (a , c) q (suc k) h with ‼-map suc c k h
  ... | y , hy , Eq.refl = ‼-in₂ (λ i → S (suc i)) k (Eq.subst (λ p → proj₂ p ‼ k ≡ just y) (Eq.sym q) hy)
  go true  e (a , c) q k h with ‼-map suc c k h
  ... | y , hy , Eq.refl = ‼-in₂ (λ i → S (suc i)) k (Eq.subst (λ p → proj₂ p ‼ k ≡ just y) (Eq.sym q) hy)

-- An entry of a concatenation.
‼-++ : {A : Set} (xs ys : List A) (k : ℕ) {x : A} → (xs ++ ys) ‼ k ≡ just x →
       ((k <ᵇ length xs) ≡ true × xs ‼ k ≡ just x) ⊎ ((k <ᵇ length xs) ≡ false × ys ‼ (k ∸ length xs) ≡ just x)
‼-++ []       ys k       h = inj₂ (Eq.refl , h)
‼-++ (x ∷ xs) ys zero    h = inj₁ (Eq.refl , h)
‼-++ (x ∷ xs) ys (suc k) h with ‼-++ xs ys k h
... | inj₁ p = inj₁ p
... | inj₂ p = inj₂ p

-- Every index below the length has an entry.
‼-total : {A : Set} (xs : List A) (k : ℕ) → k < length xs → Σ A (λ x → xs ‼ k ≡ just x)
‼-total (x ∷ xs) zero    _       = x , Eq.refl
‼-total (x ∷ xs) (suc k) (s≤s p) = ‼-total xs k p

-- The k-th entry of ts S is in S exactly when k is below the weight.
‼-ts : (S : Fin n → Bool) (k : ℕ) {x : Fin n} → ts S ‼ k ≡ just x → S x ≡ (k <ᵇ weight S)
‼-ts S k {x} h with ‼-++ (proj₁ (part S)) (proj₂ (part S)) k h
... | inj₁ (lt , h₁) = Eq.trans (‼-in₁ S k h₁) (Eq.sym lt)
... | inj₂ (ge , h₂) = Eq.trans (‼-in₂ S (k ∸ weight S) h₂) (Eq.sym ge)

------------------------------------------------------------------------
-- The partition list is distinct

private
  avoid-map : {t : Fin n} (xs : List (Fin n)) → Avoid t xs → Avoid (suc t) (map suc xs)
  avoid-map []       CF.[]       = CF.[]
  avoid-map (x ∷ xs) (p CF.∷ a) = (λ e → p (FinP.suc-injective e)) CF.∷ avoid-map xs a

  avoid-0 : (xs : List (Fin n)) → Avoid zero (map suc xs)
  avoid-0 []       = CF.[]
  avoid-0 (x ∷ xs) = (λ ()) CF.∷ avoid-0 xs

  distinct-map : (xs : List (Fin n)) → Distinct xs → Distinct (map suc xs)
  distinct-map []       CF.[]       = CF.[]
  distinct-map (x ∷ xs) (a CF.∷ d) = avoid-map xs a CF.∷ distinct-map xs d

  map-++ : {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f []       ys = Eq.refl
  map-++ f (x ∷ xs) ys = Eq.cong (f x ∷_) (map-++ f xs ys)

  avoid-++ : {t : Fin n} (xs ys : List (Fin n)) → Avoid t (xs ++ ys) → (∀ {y} → t ≢ y → Avoid t (xs ++ y ∷ ys))
  avoid-++ []       ys a       p = p CF.∷ a
  avoid-++ (x ∷ xs) ys (q CF.∷ a) p = q CF.∷ avoid-++ xs ys a p

  -- A state inserted in the middle of a distinct list it avoids.
  insert-mid : (xs ys : List (Fin n)) (t : Fin n) → Avoid t (xs ++ ys) → Distinct (xs ++ ys) →
               Distinct (xs ++ t ∷ ys)
  insert-mid []       ys t a d                = a CF.∷ d
  insert-mid (x ∷ xs) ys t (p CF.∷ a) (b CF.∷ d) =
    avoid-++ xs ys b (λ e → p (Eq.sym e)) CF.∷ insert-mid xs ys t a d

  step-distinct : (b : Bool) (p : List (Fin n) × List (Fin n)) → Distinct (proj₁ p ++ proj₂ p) →
                  Distinct (proj₁ (step b p) ++ proj₂ (step b p))
  step-distinct true  (a , c) d =
    Eq.subst (λ z → Distinct (zero ∷ z)) (map-++ suc a c) (avoid-0 (a ++ c) CF.∷ distinct-map (a ++ c) d)
  step-distinct false (a , c) d =
    insert-mid (map suc a) (map suc c) zero
      (Eq.subst (Avoid zero) (map-++ suc a c) (avoid-0 (a ++ c)))
      (Eq.subst Distinct (map-++ suc a c) (distinct-map (a ++ c) d))

ts-distinct : (S : Fin n → Bool) → Distinct (ts S)
ts-distinct {zero}  S = CF.[]
ts-distinct {suc n} S = step-distinct (S zero) (part (λ i → S (suc i))) (ts-distinct (λ i → S (suc i)))

------------------------------------------------------------------------
-- Deciding distinctness, and the frame of a list

av : {t x : Fin n} {xs : List (Fin n)} → Dec (t ≡ x) → Maybe (Avoid t xs) → Maybe (Avoid t (x ∷ xs))
av (no ne) (just a) = just (ne CF.∷ a)
av _       _        = nothing

avoid? : (t : Fin n) (xs : List (Fin n)) → Maybe (Avoid t xs)
avoid? t []       = just CF.[]
avoid? t (x ∷ xs) = av (t FinP.≟ x) (avoid? t xs)

ds : {t : Fin n} {xs : List (Fin n)} → Maybe (Avoid t xs) → Maybe (Distinct xs) → Maybe (Distinct (t ∷ xs))
ds (just a) (just d) = just (a CF.∷ d)
ds _        _        = nothing

distinct? : (xs : List (Fin n)) → Maybe (Distinct xs)
distinct? []       = just CF.[]
distinct? (t ∷ xs) = ds (avoid? t xs) (distinct? xs)

avoid?-complete : (t : Fin n) (xs : List (Fin n)) → Avoid t xs → Σ (Avoid t xs) (λ a → avoid? t xs ≡ just a)
avoid?-complete t []       CF.[]       = CF.[] , Eq.refl
avoid?-complete t (x ∷ xs) (p CF.∷ a) = go (t FinP.≟ x) (avoid?-complete t xs a)
  where
  go : (d : Dec (t ≡ x)) → Σ (Avoid t xs) (λ a′ → avoid? t xs ≡ just a′) →
       Σ (Avoid t (x ∷ xs)) (λ a′ → av d (avoid? t xs) ≡ just a′)
  go (yes e) _         = ⊥-elim (p e)
  go (no ne) (a′ , e′) = ne CF.∷ a′ , Eq.cong (av (no ne)) e′

distinct?-complete : (xs : List (Fin n)) → Distinct xs → Σ (Distinct xs) (λ d → distinct? xs ≡ just d)
distinct?-complete []       CF.[]       = CF.[] , Eq.refl
distinct?-complete (t ∷ xs) (a CF.∷ d) = go (avoid?-complete t xs a) (distinct?-complete xs d)
  where
  go : Σ (Avoid t xs) (λ a′ → avoid? t xs ≡ just a′) → Σ (Distinct xs) (λ d′ → distinct? xs ≡ just d′) →
       Σ (Distinct (t ∷ xs)) (λ d′ → ds (avoid? t xs) (distinct? xs) ≡ just d′)
  go (a′ , ea) (d′ , ed) = a′ CF.∷ d′ , Eq.cong₂ ds ea ed

fr : (xs : List (Fin n)) → Maybe (Distinct xs) → Word (SG n)
fr xs (just d) = frame xs d
fr xs nothing  = ε

-- The frame of a list of states (ε when they are not distinct): it
-- sends the state i to the i-th entry.
frameL : List (Fin n) → Word (SG n)
frameL xs = fr xs (distinct? xs)

frameL-act : (xs : List (Fin n)) → Distinct xs → (i x : Fin n) → xs ‼ toℕ i ≡ just x → actₙ (frameL xs) i ≡ x
frameL-act xs d i x h = go (distinct?-complete xs d)
  where
  go : Σ (Distinct xs) (λ d′ → distinct? xs ≡ just d′) → actₙ (frameL xs) i ≡ x
  go (d′ , e) = Eq.subst (λ m → actₙ (fr xs m) i ≡ x) (Eq.sym e) (frame-act xs d′ i x h)

------------------------------------------------------------------------
-- The size of a subset is invariant under permutations

private
  open Sum ℕP.+-0-commutativeMonoid using (sum ; sum-permute)

  ind : (Fin n → Bool) → Fin n → ℕ
  ind S i = if S i then 1 else 0

  weight-step : (b : Bool) (p : List (Fin n) × List (Fin n)) →
                length (proj₁ (step b p)) ≡ (if b then 1 else 0) + length (proj₁ p)
  weight-step true  (a , c) = Eq.cong suc (length-map suc a)
  weight-step false (a , c) = length-map suc a

weight-sum : (S : Fin n → Bool) → weight S ≡ sum (ind S)
weight-sum {zero}  S = Eq.refl
weight-sum {suc n} S =
  Eq.trans (weight-step (S zero) (part (λ i → S (suc i))))
    (Eq.cong ((if S zero then 1 else 0) +_) (weight-sum (λ i → S (suc i))))

weight-perm : (π : Permutation′ n) (S : Fin n → Bool) → weight (λ i → S (π ⟨$⟩ʳ i)) ≡ weight S
weight-perm π S =
  Eq.trans (weight-sum (λ i → S (π ⟨$⟩ʳ i)))
    (Eq.trans (Eq.sym (sum-permute (ind S) π)) (Eq.sym (weight-sum S)))

------------------------------------------------------------------------
-- Signs

sign-liftN : (j : ℕ) (π : Permutation′ m) → sign (liftN j π) ≡ sign π
sign-liftN zero    π = Eq.refl
sign-liftN (suc j) π = Eq.trans (sign-lift₀ (liftN j π)) (sign-liftN j π)

-- A permutation that agrees with a lifted one has its sign.
sign-by-liftN : (j : ℕ) (π : Permutation′ (j + m)) (ρ : Permutation′ m) →
                (∀ i → π ⟨$⟩ʳ i ≡ liftN j ρ ⟨$⟩ʳ i) → sign π ≡ sign ρ
sign-by-liftN j π ρ e = Eq.trans (sign-cong {π = π} {ρ = liftN j ρ} e) (sign-liftN j ρ)

private
  xor-cancel : (x y : Bool) → x xor (y xor x) ≡ y
  xor-cancel false y = Eq.trans (xor-comm y false) Eq.refl
  xor-cancel true  y = Eq.trans (Eq.cong (true xor_) (xor-comm y true)) (not-not y)
    where
    not-not : ∀ b → true xor (true xor b) ≡ b
    not-not false = Eq.refl
    not-not true  = Eq.refl

-- A permutation between two copies of another has its sign.
sign-sandwich : (ρ π : Permutation′ n) → sign (ρ ∘ₚ (π ∘ₚ ρ)) ≡ sign π
sign-sandwich ρ π =
  Eq.trans (sign-∘ ρ (π ∘ₚ ρ))
    (Eq.trans (Eq.cong (sign ρ xor_) (sign-∘ π ρ)) (xor-cancel (sign ρ) (sign π)))
