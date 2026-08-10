------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of modular arithmetic on ℤ/nℤ
--
-- ℤ/nℤ is a commutative ring for every n; the structures and bundles
-- are assembled at the end of the file.
--
-- (Staged in ForStdlib for upstreaming into Data.Fin.Mod.Properties.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Mod.Properties where

open import Agda.Builtin.FromNat using (fromNat)
open import Algebra.Bundles using (AbelianGroup ; CommutativeRing ; Group ; Ring)
open import Algebra.Consequences.Propositional
  using (comm∧idˡ⇒idʳ ; comm∧distrˡ⇒distrʳ ; comm∧invˡ⇒invʳ ; comm∧zeˡ⇒zeʳ)
open import Algebra.Definitions
open import Algebra.Structures using (IsAbelianGroup ; IsCommutativeRing)
open import Data.Fin.Base using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties
  using (fromℕ<-cong ; fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ<n)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.DivMod
  using (_%_ ; m%n<n ; n%n≡0 ; m<n⇒m%n≡m ; %-distribˡ-+ ; %-distribˡ-*)
open import Data.Nat.Properties as NP using (n<1+n)
open import Data.Product.Base using (_,_)
-- ⊤ is the Constraint that Data.Fin.Literals attaches to a numeric
-- literal; its instance has to be in scope wherever one is written.
open import Data.Unit.Base using (⊤)
open import Level using (0ℓ)
open import Notations using (auto ; ₀ ; ₁ ; ₁₊ ; ₂₊)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

open import ForStdlib.Data.Fin.Mod.Base

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Powers and the top residue

lemma-0^′k : ∀ k → _^′_ {n} 0₂₊ₙ (₁₊ k) ≡ 0₂₊ₙ
lemma-0^′k k = refl

lemma-toℕ₋₁ : toℕ (₋₁ {n}) ≡ n
lemma-toℕ₋₁ {n@0} = auto
lemma-toℕ₋₁ {n@(₁₊ n')} = begin
  toℕ ₋₁ ≡⟨ cong ₁₊ lemma-toℕ₋₁ ⟩
  n ∎
  where
  open ≡-Reasoning



+-cong : Congruent₂ (_≡_ {A = ℤ n}) _+_
+-cong {x} {y} {u} {v} ≡.refl ≡.refl = ≡.refl

+-identityˡ : LeftIdentity (_≡_ {A = ℤ (₁₊ n)}) 0 _+_
+-identityˡ {n} a = begin
  fromℕ< ((m%n<n (0 ℕ.+ toℕ a) (₁₊ n))) ≡⟨ refl ⟩
  fromℕ< ((m%n<n (toℕ a) (₁₊ n))) ≡⟨ fromℕ<-cong ((toℕ a) % (₁₊ n)) (toℕ a) (m<n⇒m%n≡m (toℕ<n a)) ((m%n<n (toℕ a) (₁₊ n))) (toℕ<n a) ⟩
  fromℕ< (toℕ<n a) ≡⟨ fromℕ<-toℕ a (toℕ<n a) ⟩
  a ∎
  where open ≡.≡-Reasoning

+-assoc : Associative (_≡_ {A = ℤ n}) _+_
+-assoc {₁₊ n} a b c = begin
  a + b + c ≡⟨ refl ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n))) + c ≡⟨ refl ⟩
  fromℕ< (((m%n<n (toℕ (fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n)))) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ cong (\ x → fromℕ< (((m%n<n (x ℕ.+ toℕ c) (₁₊ n))))) (toℕ-fromℕ< (m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n))) ⟩
  fromℕ< (((m%n<n ((toℕ a ℕ.+ toℕ b) % (₁₊ n) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ cong (\ x → fromℕ< (((m%n<n (x ℕ.+ toℕ c) (₁₊ n))))) (%-distribˡ-+ (toℕ a) (toℕ b) (₁₊ n)) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ cong (\ x → fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ x) (₁₊ n))))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) (₁₊ n)))) ≡⟨ fromℕ<-cong (((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n))  ℕ.+ toℕ c) % (₁₊ n)) (sym (%-distribˡ-+ ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n))) (toℕ c) ((₁₊ n)))) (m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) (₁₊ n)) (m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n))  ℕ.+ toℕ c) (₁₊ n)) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ (≡.cong (\ x → fromℕ< (((m%n<n (x) (₁₊ n))))) (NP.+-assoc ( toℕ a % (₁₊ n)) (toℕ b % (₁₊ n)) (toℕ c))) ⟩
  fromℕ< (((m%n<n (toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c)) (₁₊ n)))) ≡⟨ cong₂ (\ x y → fromℕ< (((m%n<n (x ℕ.+ (toℕ b % (₁₊ n) ℕ.+ y)) (₁₊ n))))) ( (m<n⇒m%n≡m (toℕ<n a))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) (₁₊ n))) ≡⟨ sym (fromℕ<-cong ((toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) % (₁₊ n)) ((toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) % (₁₊ n)) (sym (%-distribˡ-+ (toℕ a) ((toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) ((₁₊ n)))) (m%n<n (toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n)) (m%n<n (toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n))) ≡⟨ cong (\ x → fromℕ< ((m%n<n (x ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n)))) (m<n⇒m%n≡m (toℕ<n a)) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n))) ≡⟨ sym (cong (\ x → fromℕ< ((m%n<n (toℕ a ℕ.+ x) (₁₊ n)))) (%-distribˡ-+ (toℕ b) (toℕ c) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ (toℕ b ℕ.+ toℕ c) % (₁₊ n)) (₁₊ n))) ≡⟨ sym (cong (\ x → fromℕ< ((m%n<n (toℕ a ℕ.+ x) (₁₊ n)))) (toℕ-fromℕ< (m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n)))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ (fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))))) (₁₊ n))) ≡⟨ refl ⟩
  a + fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))) ≡⟨ refl ⟩
  a + (b + c) ∎
  where open ≡.≡-Reasoning

+-comm : Commutative (_≡_ {A = ℤ n }) _+_
+-comm {₁₊ n} a b = begin
  fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n))) ≡⟨ cong (\ x → fromℕ< ((m%n<n (x) (₁₊ n)))) (NP.+-comm (toℕ a) (toℕ b)) ⟩
  fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ a) (₁₊ n))) ∎
  where open ≡.≡-Reasoning

+-identityʳ : RightIdentity (_≡_ {A = ℤ (₁₊ n)}) 0 _+_
+-identityʳ = comm∧idˡ⇒idʳ +-comm +-identityˡ

+-identity : Identity (_≡_ {A = ℤ (₁₊ n)}) 0 _+_
+-identity = +-identityˡ , +-identityʳ

*-identityˡ : LeftIdentity (_≡_ {A = ℤ (₂₊ n)}) 1 _*_
*-identityˡ {n} a = begin
  fromℕ< ((m%n<n (1 ℕ.* toℕ a) (₂₊ n))) ≡⟨ cong (\ x → fromℕ< ((m%n<n (x) (₂₊ n)))) (NP.*-identityˡ (toℕ a)) ⟩
  fromℕ< ((m%n<n (toℕ a) (₂₊ n))) ≡⟨ fromℕ<-cong ((toℕ a) % (₂₊ n)) (toℕ a) (m<n⇒m%n≡m (toℕ<n a)) ((m%n<n (toℕ a) (₂₊ n))) (toℕ<n a) ⟩
  fromℕ< (toℕ<n a) ≡⟨ fromℕ<-toℕ a (toℕ<n a) ⟩
  a ∎
  where open ≡.≡-Reasoning

*-assoc : Associative (_≡_ {A = ℤ n}) _*_
*-assoc {₁₊ n} a b c = begin
  a * b * c ≡⟨ refl ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n))) * c ≡⟨ refl ⟩
  fromℕ< (((m%n<n (toℕ (fromℕ< ((m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n)))) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ cong (\ x → fromℕ< (((m%n<n (x ℕ.* toℕ c) (₁₊ n))))) (toℕ-fromℕ< (m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n))) ⟩
  fromℕ< (((m%n<n ((toℕ a ℕ.* toℕ b) % (₁₊ n) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ cong (\ x → fromℕ< (((m%n<n (x ℕ.* toℕ c) (₁₊ n))))) (%-distribˡ-* (toℕ a) (toℕ b) (₁₊ n)) ⟩
  fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ cong (\ x → fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* x) (₁₊ n))))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* (toℕ c % (₁₊ n))) (₁₊ n)))) ≡⟨ fromℕ<-cong ((((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n)) ((((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n)))  ℕ.* toℕ c) % (₁₊ n)) (sym (%-distribˡ-* (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n)))) (toℕ c) ((₁₊ n)))) (m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* (toℕ c % (₁₊ n))) (₁₊ n)) (m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n)))  ℕ.* toℕ c) (₁₊ n)) ⟩
  fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ (≡.cong (\ x → fromℕ< (((m%n<n (x) (₁₊ n))))) (NP.*-assoc ( (toℕ a % (₁₊ n))) ((toℕ b % (₁₊ n))) (toℕ c))) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n)) ℕ.* ((toℕ b % (₁₊ n)) ℕ.* toℕ c)) (₁₊ n)))) ≡⟨ cong₂ (\ x y → fromℕ< (((m%n<n (x ℕ.* ((toℕ b % (₁₊ n)) ℕ.* y)) (₁₊ n))))) ( (m<n⇒m%n≡m (toℕ<n a))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* ((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n)))) (₁₊ n))) ≡⟨ sym (fromℕ<-cong (((toℕ a % (₁₊ n)) ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) % (₁₊ n)) ((toℕ a ℕ.* ((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n)))) % (₁₊ n)) (sym (%-distribˡ-* (toℕ a) ((((toℕ b % (₁₊ n))) ℕ.* ((toℕ c % (₁₊ n))))) ((₁₊ n)))) (m%n<n ((toℕ a % (₁₊ n)) ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) (₁₊ n)) (m%n<n (toℕ a ℕ.* ((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n)))) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (((toℕ a % (₁₊ n))) ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) (₁₊ n))) ≡⟨ cong (\ x → fromℕ< ((m%n<n (x ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) (₁₊ n)))) (m<n⇒m%n≡m (toℕ<n a)) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* ((((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n)))) (₁₊ n))) ≡⟨ sym (cong (\ x → fromℕ< ((m%n<n (toℕ a ℕ.* x) (₁₊ n)))) (%-distribˡ-* (toℕ b) (toℕ c) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* ((toℕ b ℕ.* toℕ c) % (₁₊ n))) (₁₊ n))) ≡⟨ sym (cong (\ x → fromℕ< ((m%n<n (toℕ a ℕ.* x) (₁₊ n)))) (toℕ-fromℕ< (m%n<n (toℕ b ℕ.* toℕ c) (₁₊ n)))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* toℕ (fromℕ< ((m%n<n (toℕ b ℕ.* toℕ c) (₁₊ n))))) (₁₊ n))) ≡⟨ refl ⟩
  a * fromℕ< ((m%n<n (toℕ b ℕ.* toℕ c) (₁₊ n))) ≡⟨ refl ⟩
  a * (b * c) ∎
  where open ≡.≡-Reasoning

*-comm : Commutative (_≡_ {A = ℤ n }) _*_
*-comm {₁₊ n} a b = begin
  fromℕ< ((m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n))) ≡⟨ cong (\ x → fromℕ< ((m%n<n (x) (₁₊ n)))) (NP.*-comm (toℕ a) (toℕ b)) ⟩
  fromℕ< ((m%n<n (toℕ b ℕ.* toℕ a) (₁₊ n))) ∎
  where open ≡.≡-Reasoning

*-identityʳ : RightIdentity (_≡_ {A = ℤ (₂₊ n)}) 1 _*_
*-identityʳ = comm∧idˡ⇒idʳ *-comm *-identityˡ

*-identity : Identity (_≡_ {A = ℤ (₂₊ n)}) 1 _*_
*-identity = *-identityˡ , *-identityʳ


*-distribˡ-+ : _DistributesOverˡ_ (_≡_ {A = ℤ n}) _*_ _+_
*-distribˡ-+ {₁₊ n} a b c = begin
  a * (b + c) ≡⟨ refl ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* toℕ (fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))))) (₁₊ n)) ≡⟨ cong (\ x → fromℕ< (m%n<n (toℕ a ℕ.* x) (₁₊ n))) (toℕ-fromℕ< (m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n)) ≡⟨ sym (cong (\ x → fromℕ< (m%n<n (x ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n))) (m<n⇒m%n≡m (toℕ<n a))) ⟩
  fromℕ< (m%n<n (toℕ a % (₁₊ n) ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n)) ≡⟨ fromℕ<-cong ((toℕ a % (₁₊ n) ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) % (₁₊ n)) ((toℕ a ℕ.* (toℕ b ℕ.+ toℕ c)) % (₁₊ n)) (sym (%-distribˡ-* (toℕ a) ((toℕ b ℕ.+ toℕ c)) ((₁₊ n)))) (m%n<n (toℕ a % (₁₊ n) ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n)) (m%n<n (toℕ a ℕ.* (toℕ b ℕ.+ toℕ c)) (₁₊ n)) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* (toℕ b ℕ.+ toℕ c)) (₁₊ n)) ≡⟨ cong (\ x → fromℕ< (m%n<n (x) (₁₊ n))) (NP.*-distribˡ-+ (toℕ a) (toℕ b) (toℕ c)) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* toℕ b ℕ.+ toℕ a ℕ.* toℕ c) (₁₊ n)) ≡⟨ fromℕ<-cong ((toℕ a ℕ.* toℕ b ℕ.+ toℕ a ℕ.* toℕ c) % (₁₊ n)) ((toℕ a ℕ.* toℕ b % (₁₊ n) ℕ.+ toℕ a ℕ.* toℕ c %(₁₊ n)) % (₁₊ n)) (%-distribˡ-+ (toℕ a ℕ.* toℕ b) (toℕ a ℕ.* toℕ c) ((₁₊ n))) (m%n<n (toℕ a ℕ.* toℕ b ℕ.+ toℕ a ℕ.* toℕ c) (₁₊ n)) (m%n<n (toℕ a ℕ.* toℕ b % (₁₊ n) ℕ.+ toℕ a ℕ.* toℕ c %(₁₊ n)) (₁₊ n)) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* toℕ b % (₁₊ n) ℕ.+ toℕ a ℕ.* toℕ c %(₁₊ n)) (₁₊ n)) ≡⟨ refl ⟩
  fromℕ< (m%n<n ((toℕ a ℕ.* toℕ b) % (₁₊ n) ℕ.+ (toℕ a ℕ.* toℕ c) % (₁₊ n)) (₁₊ n)) ≡⟨ sym (cong₂ (\ x y → fromℕ< (m%n<n (x ℕ.+ y) (₁₊ n))) (toℕ-fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (b)) (₁₊ n))) (toℕ-fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (c)) (₁₊ n)))) ⟩
  fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (b)) (₁₊ n))) ℕ.+ toℕ (fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (c)) (₁₊ n)))) (₁₊ n)) ≡⟨ refl ⟩
  fromℕ< (m%n<n (toℕ (a * b) ℕ.+ toℕ (a * c)) (₁₊ n)) ≡⟨ refl ⟩
  a * b + a * c ∎
  where open ≡.≡-Reasoning


*-distribʳ-+ : _DistributesOverʳ_ (_≡_ {A = ℤ n}) _*_ _+_
*-distribʳ-+ = comm∧distrˡ⇒distrʳ *-comm *-distribˡ-+

*-distrib-+ : _DistributesOver_ (_≡_ {A = ℤ n}) _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

₊₁+₋₁≡₀ : ₊₁ {n} + ₋₁ ≡ ₀
₊₁+₋₁≡₀ {n} = begin
  ₊₁ {n} + ₋₁ ≡⟨ refl ⟩
  (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ toℕ (₋₁ {₁₊ n})) (₂₊ n))) ≡⟨ refl ⟩
  (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ toℕ (fromℕ< (n<1+n (₁₊ n)))) (₂₊ n))) ≡⟨ cong (\ x → (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ x) (₂₊ n)))) (toℕ-fromℕ< (n<1+n (₁₊ n))) ⟩
  (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ (₁₊ n)) (₂₊ n))) ≡⟨ refl ⟩
  (fromℕ< (m%n<n (1 ℕ.+ (₁₊ n)) (₂₊ n))) ≡⟨ refl ⟩
  (fromℕ< (m%n<n (₂₊ n) (₂₊ n))) ≡⟨ fromℕ<-cong ((₂₊ n) % (₂₊ n)) ₀ (n%n≡0 (₂₊ n)) (m%n<n (₂₊ n) (₂₊ n)) (NP.0<1+n {₁₊ n}) ⟩
  fromℕ< (NP.0<1+n {₁₊ n}) ≡⟨ refl ⟩
  ₀ ∎
  where open ≡.≡-Reasoning

₋₁+₊₁≡₀ : ₋₁ {₁₊ n} + ₊₁ ≡ ₀
₋₁+₊₁≡₀ {n} = begin
  ₋₁ + ₊₁ {n} ≡⟨ +-comm ₋₁ ₊₁ ⟩
  ₊₁ {n} + ₋₁ ≡⟨ ₊₁+₋₁≡₀ ⟩
  ₀ ∎
  where open ≡.≡-Reasoning

+-inverseˡ : LeftInverse (_≡_ {A = ℤ (₂₊ n)}) 0 -_ _+_
+-inverseˡ {n} a = begin
  - a + a ≡⟨ cong (\ x → - a + x) (sym (*-identityˡ a)) ⟩
  - a + ₁ * a ≡⟨ sym (*-distribʳ-+ a ₋₁ ₁) ⟩
  (₋₁ + ₁) * a ≡⟨ cong (_* a) ₋₁+₊₁≡₀ ⟩
  ₀ * a ≡⟨ refl ⟩
  0 ∎
  where
  open ≡.≡-Reasoning


+-inverseʳ : RightInverse (_≡_ {A = ℤ (₂₊ n)}) 0 -_ _+_
+-inverseʳ = comm∧invˡ⇒invʳ +-comm +-inverseˡ

+-inverse : Inverse (_≡_ {A = ℤ (₂₊ n)}) 0 -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

neg-cong : Congruent₁ (_≡_ {A = ℤ (₁₊ n)}) -_
neg-cong ≡.refl = ≡.refl

+-0-isAbelianGroup : IsAbelianGroup (_≡_ {A = ℤ (₂₊ n)}) _+_ 0 -_
+-0-isAbelianGroup = record
  { isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≡.isEquivalence
          ; ∙-cong = +-cong
          }
        ; assoc = +-assoc
        }
      ; identity = +-identity
      }
    ; inverse = +-inverse
    ; ⁻¹-cong = neg-cong
    }
  ; comm = +-comm
  }

+-*-isCommutativeRing : IsCommutativeRing (_≡_ {A = ℤ (₂₊ n)}) _+_ _*_ -_ 0 1
+-*-isCommutativeRing = record
  { isRing = record
              { +-isAbelianGroup = +-0-isAbelianGroup
              ; *-cong = cong₂ _*_
              ; *-assoc = *-assoc
              ; *-identity = *-identity 
              ; distrib = *-distrib-+
              }
  ; *-comm = *-comm
  }

*-zeroˡ : LeftZero (_≡_ {A = ℤ (₁₊ n)}) 0 _*_
*-zeroˡ {n} a = refl

*-zeroʳ : RightZero (_≡_ {A = ℤ (₁₊ n)}) 0 _*_
*-zeroʳ = comm∧zeˡ⇒zeʳ *-comm *-zeroˡ



+-*-commutativeRing : ℕ → CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing n = record
  { isCommutativeRing = +-*-isCommutativeRing {n}
  }

+-*-ring : ℕ → Ring 0ℓ 0ℓ
+-*-ring n = record
  { isRing = IsCommutativeRing.isRing (+-*-isCommutativeRing {n})
  }

+-0-abelianGroup : ℕ → AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup n = record
  { isAbelianGroup = +-0-isAbelianGroup {n}
  }

+-0-group : ℕ → Group 0ℓ 0ℓ
+-0-group n = record
  { isGroup = IsAbelianGroup.isGroup (+-0-isAbelianGroup {n})
  }




1＊x=x : ∀ (x : ℤ (₁₊ n)) → ₁ ＊ x ≡ x
1＊x=x x = +-identityʳ x
