------------------------------------------------------------------------
-- Force every entry and rebuild the resulting matrix. Keeping the
-- evaluated data, rather than returning the unevaluated argument,
-- prevents repeated expansion of long products in conversion checks.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.StrictMatrix where

open import Data.Integer.Base using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra

forceℕ : ∀ {B : Set} → ℕ → (ℕ → B) → B
forceℕ zero f = f zero
forceℕ (suc n) f = forceℕ n (λ m → f (suc m))

forceℤ : ∀ {B : Set} → ℤ → (ℤ → B) → B
forceℤ (+ n) f = forceℕ n (λ m → f (+ m))
forceℤ (-[1+ n ]) f = forceℕ n (λ m → f (-[1+ m ]))

force𝔽 : ∀ {B : Set} → 𝔽 → (𝔽 → B) → B
force𝔽 (a +√2 b) f = forceℤ a (λ a′ → forceℤ b (λ b′ → f (a′ +√2 b′)))

forceTab : ∀ {B : Set} → (k : ℕ) → Tab k 𝔽 → (Tab k 𝔽 → B) → B
forceTab zero a f = force𝔽 a f
forceTab (suc k) (l , r) f = forceTab k l
  (λ l′ → forceTab k r (λ r′ → f (l′ , r′)))

forceℕ-id : ∀ {B : Set} (n : ℕ) (f : ℕ → B) → forceℕ n f ≡ f n
forceℕ-id zero f = Eq.refl
forceℕ-id (suc n) f = forceℕ-id n (λ m → f (suc m))

forceℤ-id : ∀ {B : Set} (a : ℤ) (f : ℤ → B) → forceℤ a f ≡ f a
forceℤ-id (+ n) f = forceℕ-id n (λ m → f (+ m))
forceℤ-id (-[1+ n ]) f = forceℕ-id n (λ m → f (-[1+ m ]))

force𝔽-id : ∀ {B : Set} (a : 𝔽) (f : 𝔽 → B) → force𝔽 a f ≡ f a
force𝔽-id (a +√2 b) f = Eq.trans
  (forceℤ-id a (λ a′ → forceℤ b (λ b′ → f (a′ +√2 b′))))
  (forceℤ-id b (λ b′ → f (a +√2 b′)))

forceTab-id : ∀ {B : Set} (k : ℕ) (t : Tab k 𝔽)
              (f : Tab k 𝔽 → B) → forceTab k t f ≡ f t
forceTab-id zero t f = force𝔽-id t f
forceTab-id (suc k) (l , r) f = Eq.trans
  (forceTab-id k l (λ l′ → forceTab k r (λ r′ → f (l′ , r′))))
  (forceTab-id k r (λ r′ → f (l , r′)))

strictM : Mat 3 → Mat 3
strictM (mat t) = forceTab 6 t mat

strictM-id : (M : Mat 3) → strictM M ≡ M
strictM-id (mat t) = forceTab-id 6 t mat

mul : Mat 3 → Mat 3 → Mat 3
mul M N = strictM (mulM M N)

ix-mul′ : (M N : Mat 3) → ix (mul M N) ≐ (ix M ⊙ ix N)
ix-mul′ M N x y = Eq.trans
  (Eq.cong (λ A → ix A x y) (strictM-id (mulM M N)))
  (ix-mul M N x y)
