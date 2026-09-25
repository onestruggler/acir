------------------------------------------------------------------------
-- Presentations of groups
--
-- Identities in an arbitrary commutative ring (with propositional
-- equality), for use at 𝔻[i].
--
-- They are proved here, once, with the ring solver over an ABSTRACT
-- ring.  Solving them at 𝔻[i] itself is prohibitively slow: its
-- elements are records, and the conversion check η-expands them and
-- unfolds EucDomain's dyadic arithmetic on the resulting stuck terms.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Examples.Groups.Clifford+CS-TwoLevel.Algebra
  (R : CommutativeRing 0ℓ 0ℓ)
  (let open CommutativeRing R using (_≈_))
  (≈⇒≡ : ∀ {x y} → x ≈ y → x ≡ y)
  where

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (refl ; cong ; cong₂ ; sym ; trans)
import Quantum.Synthesis.Ring.Properties.Common as Common

open import Data.Integer.Base using (+_)
open CommutativeRing R using () renaming (refl to ≈-refl)
open CommutativeRing R
  using (Carrier ; _+_ ; _*_ ; -_ ; _-_ ; 0# ; 1#)

private
  module S = Common.ZSolver R
  open S using (solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_)
  A = Carrier

------------------------------------------------------------------------
-- Powers

infixr 8 _^_

_^_ : A → ℕ → A
x ^ zero  = 1#
x ^ suc k = x * (x ^ k)

------------------------------------------------------------------------
-- Rearrangements

*-4 : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
*-4 a b c d = ≈⇒≡ (solve 4 (λ a b c d → (a :* b) :* (c :* d) := (a :* c) :* (b :* d)) ≈-refl a b c d)


*-3 : ∀ a b c → a * (b * c) ≡ b * (a * c)
*-3 a b c = ≈⇒≡ (solve 3 (λ a b c → a :* (b :* c) := b :* (a :* c)) ≈-refl a b c)


+-*-distrib : ∀ c a b → (a + b) * c ≡ a * c + b * c
+-*-distrib c a b = ≈⇒≡ (solve 3 (λ c a b → (a :+ b) :* c := a :* c :+ b :* c) ≈-refl c a b)


*-+-distrib : ∀ c a b → c * (a + b) ≡ c * a + c * b
*-+-distrib c a b = ≈⇒≡ (solve 3 (λ c a b → c :* (a :+ b) := c :* a :+ c :* b) ≈-refl c a b)


-‿*-distrib : ∀ c a → (- a) * c ≡ - (a * c)
-‿*-distrib c a = ≈⇒≡ (solve 2 (λ c a → (:- a) :* c := :- (a :* c)) ≈-refl c a)


*-‿distrib : ∀ c a → c * (- a) ≡ - (c * a)
*-‿distrib c a = ≈⇒≡ (solve 2 (λ c a → c :* (:- a) := :- (c :* a)) ≈-refl c a)


-‿*-cancel : ∀ a b → (- a) * (- b) ≡ a * b
-‿*-cancel a b = ≈⇒≡ (solve 2 (λ a b → (:- a) :* (:- b) := a :* b) ≈-refl a b)


*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc a b c = ≈⇒≡ (solve 3 (λ a b c → (a :* b) :* c := a :* (b :* c)) ≈-refl a b c)


*-comm : ∀ a b → a * b ≡ b * a
*-comm a b = ≈⇒≡ (solve 2 (λ a b → a :* b := b :* a) ≈-refl a b)


*-identityˡ : ∀ a → 1# * a ≡ a
*-identityˡ a = ≈⇒≡ (solve 1 (λ a → S.con (+ 1) :* a := a) ≈-refl a)


------------------------------------------------------------------------
-- Powers

^-+ : ∀ x m n → x ^ (m ℕ.+ n) ≡ (x ^ m) * (x ^ n)
^-+ x zero n = sym (*-identityˡ _)
^-+ x (suc m) n = trans (cong (x *_) (^-+ x m n)) (sym (*-assoc x (x ^ m) (x ^ n)))

^-*-distrib : ∀ x y k → (x * y) ^ k ≡ (x ^ k) * (y ^ k)
^-*-distrib x y zero = sym (*-identityˡ 1#)
^-*-distrib x y (suc k) =
  trans (cong ((x * y) *_) (^-*-distrib x y k)) (*-4 x y (x ^ k) (y ^ k))

1^ : ∀ k → 1# ^ k ≡ 1#
1^ zero = refl
1^ (suc k) = trans (*-identityˡ _) (1^ k)

-- If a * b = 1 then aᵏ * bᵏ = 1.
^-inverse : ∀ a b k → a * b ≡ 1# → (a ^ k) * (b ^ k) ≡ 1#
^-inverse a b k ab = trans (sym (^-*-distrib a b k)) (trans (cong (_^ k) ab) (1^ k))
