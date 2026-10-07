------------------------------------------------------------------------
-- Presentations of groups
--
-- One qubit: the two finite computations
--
-- Which pairs of codes the 24 words send X and Z to (check-table, table,
-- table-nc), and that those 24 pairs are distinct (check-inverse,
-- inverse).  Part of PathSum.Hierarchy.OneQubit.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.OneQubit.Table (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _∨_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _%_; _/_)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n; n%d<d)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using
  (_≟_; *-zeroʳ; *-identityʳ; +-identityˡ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; _<_; z≤n; s≤s)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; lookup)
  renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary.Decidable using
  (⌊_⌋; yes; no; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using
  ([_]ᶻ; _=ᵇ_; =ᵇ-refl; =ᵇ-true; same; same-≗; ≔-here)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; zpow-≡; scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; -ᴬ_; _≐_; Σᴮ-cong; zpow; rot; rot-exp; rot-0; rot-anti;
   scale-injective; N)
  renaming (H to Hᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Gates M₀
open import PathSum.Hierarchy.Levels M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ--; ≡ᴺ-N)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong)
open import PathSum.Ring.Laws M₀ using (⊛-comm)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

open import PathSum.Hierarchy.OneQubit.Code M₀
open import PathSum.Hierarchy.OneQubit.Words M₀

private
  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The computations

-- Boolean equality of codes.

_=ᶜ_ : Code → Code → Bool
c =ᶜ d = ⌊ cph c ≟ cph d ⌋ ∧ ((cx c =ᵇ cx d) ∧ (cz c =ᵇ cz d))

=ᶜ-refl : (c : Code) → (c =ᶜ c) ≡ true
=ᶜ-refl (code a x z) =
  trans (cong (λ b → b ∧ ((x =ᵇ x) ∧ (z =ᵇ z))) (=ᶻ-refl a))
        (cong₂ _∧_ (=ᵇ-refl x) (=ᵇ-refl z))

=ᶜ-sound : (c d : Code) → (c =ᶜ d) ≡ true → c ≡ d
=ᶜ-sound (code a x z) (code b x′ z′) h =
  join (=ᶻ-sound a b (∧-l ⌊ a ≟ b ⌋ ((x =ᵇ x′) ∧ (z =ᵇ z′)) h))
       (=ᵇ-true {x} {x′} (∧-l (x =ᵇ x′) (z =ᵇ z′)
                               (∧-r ⌊ a ≟ b ⌋ ((x =ᵇ x′) ∧ (z =ᵇ z′)) h)))
       (=ᵇ-true {z} {z′} (∧-r (x =ᵇ x′) (z =ᵇ z′)
                               (∧-r ⌊ a ≟ b ⌋ ((x =ᵇ x′) ∧ (z =ᵇ z′)) h)))
  where
  join : ∀ {a b x x′ z z′} → a ≡ b → x ≡ x′ → z ≡ z′ →
         code a x z ≡ code b x′ z′
  join refl refl refl = refl

-- The conditions on the images of X and Z.

herm nonid : Code → Bool
herm c  = nc (invᶜ c) =ᶜ c
nonid c = cx c ∨ cz c

differ : Code → Code → Bool
differ c d = not ((cx c =ᵇ cx d) ∧ (cz c =ᵇ cz d))

ok : Code → Code → Bool
ok c d = herm c ∧ (herm d ∧ (nonid c ∧ (nonid d ∧ differ c d)))

-- What each word does to X and Z, normalised.

keyX keyZ : Fin 24 → Code
keyX i = nc (actW (lookup words i) cX)
keyZ i = nc (actW (lookup words i) cZ)

-- The first word sending X and Z to c and d (the last, if none does).

search : {m : ℕ} → (Fin (suc m) → Bool) → Fin (suc m)
search {zero}  f = zero
search {suc m} f = if f zero then zero else suc (search (λ i → f (suc i)))

look : Code → Code → Fin 24
look c d = search (λ i → (keyX i =ᶜ c) ∧ (keyZ i =ᶜ d))

-- Enumerations.

allB : (Bool → Bool) → Bool
allB f = f false ∧ f true

allB-sound : (f : Bool → Bool) → allB f ≡ true → ∀ b → f b ≡ true
allB-sound f h false = ∧-l (f false) (f true) h
allB-sound f h true  = ∧-r (f false) (f true) h

allK : (ℕ → Bool) → Bool
allK f = f 0 ∧ (f 1 ∧ (f 2 ∧ f 3))

allK-sound : (f : ℕ → Bool) → allK f ≡ true → ∀ k → k < 4 → f k ≡ true
allK-sound f h 0 _ = ∧-l (f 0) (f 1 ∧ (f 2 ∧ f 3)) h
allK-sound f h 1 _ =
  ∧-l (f 1) (f 2 ∧ f 3) (∧-r (f 0) (f 1 ∧ (f 2 ∧ f 3)) h)
allK-sound f h 2 _ =
  ∧-l (f 2) (f 3) (∧-r (f 1) (f 2 ∧ f 3) (∧-r (f 0) (f 1 ∧ (f 2 ∧ f 3)) h))
allK-sound f h 3 _ =
  ∧-r (f 2) (f 3) (∧-r (f 1) (f 2 ∧ f 3) (∧-r (f 0) (f 1 ∧ (f 2 ∧ f 3)) h))
allK-sound f h (suc (suc (suc (suc k)))) (s≤s (s≤s (s≤s (s≤s ()))))

allC : (Code → Bool) → Bool
allC f = allK (λ k → allB (λ x → allB (λ z → f (code (+ k) x z))))

allC-sound : (f : Code → Bool) → allC f ≡ true →
             ∀ k x z → k < 4 → f (code (+ k) x z) ≡ true
allC-sound f h k x z k<4 =
  allB-sound (λ z → f (code (+ k) x z))
    (allB-sound (λ x → allB (λ z → f (code (+ k) x z)))
      (allK-sound (λ k → allB (λ x → allB (λ z → f (code (+ k) x z))))
                  h k k<4)
      x)
    z

allFin : {m : ℕ} → (Fin m → Bool) → Bool
allFin {zero}  f = true
allFin {suc m} f = f zero ∧ allFin (λ i → f (suc i))

allFin-sound : {m : ℕ} (f : Fin m → Bool) → allFin f ≡ true →
               ∀ i → f i ≡ true
allFin-sound {suc m} f h zero    =
  ∧-l (f zero) (allFin (λ i → f (suc i))) h
allFin-sound {suc m} f h (suc i) =
  allFin-sound (λ i → f (suc i)) (∧-r (f zero) (allFin (λ i → f (suc i))) h) i

-- Every pair of normalised codes satisfying the conditions is what
-- some word sends X and Z to.

hit : Code → Code → Bool
hit c d = (keyX (look c d) =ᶜ c) ∧ (keyZ (look c d) =ᶜ d)

row : Code → Code → Bool
row c d = not (ok c d) ∨ hit c d

table-ok : Code → Bool
table-ok c = allC (row c)

check-table : allC table-ok ≡ true
check-table = refl

-- The codes are written out in each statement below, never
-- abbreviated: two spellings of one code under look make Agda compare
-- them by running the search.

table : (k l : ℕ) (x z x′ z′ : Bool) → k < 4 → l < 4 →
        ok (code (+ k) x z) (code (+ l) x′ z′) ≡ true →
        hit (code (+ k) x z) (code (+ l) x′ z′) ≡ true
table k l x z x′ z′ k<4 l<4 okh =
  ∨-not (ok (code (+ k) x z) (code (+ l) x′ z′))
        (hit (code (+ k) x z) (code (+ l) x′ z′)) okh
    (allC-sound (row (code (+ k) x z))
                (allC-sound table-ok check-table k x z k<4) l x′ z′ l<4)

table-nc : (a b : Code) → ok (nc a) (nc b) ≡ true →
           (keyX (look (nc a) (nc b)) ≡ nc a) ×
           (keyZ (look (nc a) (nc b)) ≡ nc b)
table-nc a b okh =
  =ᶜ-sound (keyX (look (nc a) (nc b))) (nc a)
    (∧-l (keyX (look (nc a) (nc b)) =ᶜ nc a)
         (keyZ (look (nc a) (nc b)) =ᶜ nc b) h) ,
  =ᶜ-sound (keyZ (look (nc a) (nc b))) (nc b)
    (∧-r (keyX (look (nc a) (nc b)) =ᶜ nc a)
         (keyZ (look (nc a) (nc b)) =ᶜ nc b) h)
  where
  h : hit (nc a) (nc b) ≡ true
  h = subst₂ (λ c d → hit c d ≡ true)
        {x = code (+ (cph a % (+ 4))) (cx a) (cz a)} {y = nc a}
        {u = code (+ (cph b % (+ 4))) (cx b) (cz b)} {v = nc b} refl refl
        (table (cph a % (+ 4)) (cph b % (+ 4)) (cx a) (cz a) (cx b) (cz b)
               (n%d<d (cph a) (+ 4)) (n%d<d (cph b) (+ 4))
               (subst₂ (λ c d → ok c d ≡ true)
                  {x = nc a} {y = code (+ (cph a % (+ 4))) (cx a) (cz a)}
                  {u = nc b} {v = code (+ (cph b % (+ 4))) (cx b) (cz b)}
                  refl refl okh))

-- The 24 words send X and Z to 24 different pairs.

inv-ok : Fin 24 → Bool
inv-ok i = ⌊ look (keyX i) (keyZ i) Fin.≟ i ⌋

check-inverse : allFin inv-ok ≡ true
check-inverse = refl

inverse : (i : Fin 24) → look (keyX i) (keyZ i) ≡ i
inverse i = =ᶠ-sound (look (keyX i) (keyZ i)) i
                     (allFin-sound inv-ok check-inverse i)
