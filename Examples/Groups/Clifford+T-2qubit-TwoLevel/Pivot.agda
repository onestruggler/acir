------------------------------------------------------------------------
-- Presentations of groups
--
-- Pivots and levels (Definition 2.15).  The pivot of a matrix is its
-- last column that differs from the identity; its level is the triple
-- (pivot + 1, lde of the pivot column, number of its odd entries), or
-- (0, 0, 0) for the identity, ordered lexicographically.  A word acting
-- only on indices ≤ p keeps the columns beyond p as they are.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; toℕ ; _<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
import Data.Nat.Induction as ℕI
open import Data.Product.Base using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex ; ×-wellFounded ; ×-decidable ; ×-irreflexive)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Induction.WellFounded using (WellFounded ; Acc ; acc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde using (lde ; num)
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column using (nodd)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Decidable equality of columns

_≟ᵛ_ : (u v : Vec D n) → Dec (u ≡ v)
_≟ᵛ_ = VecP.≡-dec _≟ᴰ_

------------------------------------------------------------------------
-- The pivot

-- Is column c of M different from the identity's?
notE : Matrix n n D → Fin n → Bool
notE M c = not (does (col M c ≟ᵛ col 𝕀 c))

pivot : Matrix n n D → Maybe (Fin n)
pivot M = last (notE M)

-- M agrees with the identity beyond column p.
Beyond : Fin n → Matrix n n D → Set
Beyond p M = ∀ c → p < c → col M c ≡ col 𝕀 c

private
  -- (Case analyses on decisions are done by helper functions, not by
  -- with-abstraction, which would normalise goals mentioning columns.)
  notE-true : (M : Matrix n n D) (c : Fin n) → notE M c ≡ true → col M c ≢ col 𝕀 c
  notE-true M c = aux (col M c ≟ᵛ col 𝕀 c)
    where
    aux : (d : Dec (col M c ≡ col 𝕀 c)) → not (does d) ≡ true → col M c ≢ col 𝕀 c
    aux (yes _) ()
    aux (no ne) _ = ne

  notE-false : (M : Matrix n n D) (c : Fin n) → notE M c ≡ false → col M c ≡ col 𝕀 c
  notE-false M c = aux (col M c ≟ᵛ col 𝕀 c)
    where
    aux : (d : Dec (col M c ≡ col 𝕀 c)) → not (does d) ≡ false → col M c ≡ col 𝕀 c
    aux (yes e) _ = e
    aux (no _) ()

  true-notE : (M : Matrix n n D) (c : Fin n) → col M c ≢ col 𝕀 c → notE M c ≡ true
  true-notE M c ne = aux (col M c ≟ᵛ col 𝕀 c)
    where
    aux : (d : Dec (col M c ≡ col 𝕀 c)) → not (does d) ≡ true
    aux (yes e) = ⊥-elim (ne e)
    aux (no _) = refl

  false-notE : (M : Matrix n n D) (c : Fin n) → col M c ≡ col 𝕀 c → notE M c ≡ false
  false-notE M c e = aux (col M c ≟ᵛ col 𝕀 c)
    where
    aux : (d : Dec (col M c ≡ col 𝕀 c)) → not (does d) ≡ false
    aux (yes _) = refl
    aux (no ne) = ⊥-elim (ne e)

pivot-just : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → col M p ≢ col 𝕀 p × Beyond p M
pivot-just M {p} eq =
  notE-true M p (proj₁ (last-just (notE M) eq)) ,
  λ c p<c → notE-false M c (proj₂ (last-just (notE M) eq) c p<c)

pivot-nothing : (M : Matrix n n D) → pivot M ≡ nothing → M ≡ 𝕀
pivot-nothing M eq = col-ext λ c → notE-false M c (last-nothing (notE M) eq c)

pivot-char : (M : Matrix n n D) {p : Fin n} → col M p ≢ col 𝕀 p → Beyond p M → pivot M ≡ just p
pivot-char M {p} ne be = last-char (notE M) (true-notE M p ne) (λ c p<c → false-notE M c (be c p<c))

pivot-𝕀 : pivot (𝕀 {n}) ≡ nothing
pivot-𝕀 = last-none (notE 𝕀) (λ c → false-notE 𝕀 c refl)

-- If M agrees with the identity from column p on, its pivot is below p.
pivot-below : (M : Matrix n n D) {p : Fin n} → col M p ≡ col 𝕀 p → Beyond p M →
              pivot M ≡ nothing ⊎ ∃ λ p′ → pivot M ≡ just p′ × p′ < p
pivot-below M {p} Mp be = aux (pivot M) refl
  where
  aux : (r : Maybe (Fin _)) → pivot M ≡ r → pivot M ≡ nothing ⊎ ∃ λ p′ → pivot M ≡ just p′ × p′ < p
  aux nothing eq = inj₁ eq
  aux (just p′) eq = tri-elim (FinP.<-cmp p′ p)
    (λ p′<p → inj₂ (p′ , eq , p′<p))
    (λ p′≡p → ⊥-elim (proj₁ (pivot-just M (trans eq (cong just p′≡p))) Mp))
    (λ p<p′ → ⊥-elim (proj₁ (pivot-just M eq) (be p′ p<p′)))

------------------------------------------------------------------------
-- Levels

Lvl : Set
Lvl = ℕ × ℕ × ℕ

infix 4 _<ₗ_ _<₂_

_<₂_ : ℕ × ℕ → ℕ × ℕ → Set
_<₂_ = ×-Lex _≡_ ℕ._<_ ℕ._<_

_<ₗ_ : Lvl → Lvl → Set
_<ₗ_ = ×-Lex _≡_ ℕ._<_ _<₂_

<ₗ-wellFounded : WellFounded _<ₗ_
<ₗ-wellFounded = ×-wellFounded ℕI.<-wellFounded (×-wellFounded ℕI.<-wellFounded ℕI.<-wellFounded)

_<ₗ?_ : (a b : Lvl) → Dec (a <ₗ b)
_<ₗ?_ = ×-decidable ℕP._≟_ ℕP._<?_ (×-decidable ℕP._≟_ ℕP._<?_ ℕP._<?_)

<ₗ-irrefl : ∀ {a : Lvl} → ¬ (a <ₗ a)
<ₗ-irrefl (inj₁ lt) = ℕP.<-irrefl refl lt
<ₗ-irrefl (inj₂ (_ , inj₁ lt)) = ℕP.<-irrefl refl lt
<ₗ-irrefl (inj₂ (_ , inj₂ (_ , lt))) = ℕP.<-irrefl refl lt

-- The level of a matrix, given its pivot.
lvlAt : Maybe (Fin n) → Matrix n n D → Lvl
lvlAt nothing  M = 0 , 0 , 0
lvlAt (just p) M = suc (toℕ p) , lde (col M p) , nodd (num (col M p))

level : Matrix n n D → Lvl
level M = lvlAt (pivot M) M

level-just : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p →
             level M ≡ (suc (toℕ p) , lde (col M p) , nodd (num (col M p)))
level-just M eq = cong (λ x → lvlAt x M) eq

-- A matrix that is the identity from column p on has level below any
-- level with pivot p.
level-below : (M : Matrix n n D) {p : Fin n} → col M p ≡ col 𝕀 p → Beyond p M →
              ∀ k m → level M <ₗ (suc (toℕ p) , k , m)
level-below M {p} Mp be k m = [ (λ eq → subst (λ x → lvlAt x M <ₗ (suc (toℕ p) , k , m)) (sym eq) (inj₁ (ℕ.s≤s ℕ.z≤n)))                               , (λ { (p′ , eq , p′<p) → subst (λ x → lvlAt x M <ₗ (suc (toℕ p) , k , m)) (sym eq) (inj₁ (ℕ.s≤s p′<p)) }) ]′                               (pivot-below M Mp be)

-- With the same pivot, the level compares the exponent and odd count.
level-same : (M : Matrix n n D) {p : Fin n} → col M p ≢ col 𝕀 p → Beyond p M →
             ∀ {k m} → (lde (col M p) , nodd (num (col M p))) <₂ (k , m) →
             level M <ₗ (suc (toℕ p) , k , m)

level-same M {p} ne be {k} {m} lt = subst (λ x → lvlAt x M <ₗ (suc (toℕ p) , k , m)) (sym (pivot-char M ne be)) (inj₂ (refl , lt))
