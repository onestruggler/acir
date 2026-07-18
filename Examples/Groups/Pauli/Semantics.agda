{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=2 #-}
open import Relation.Binary.PropositionalEquality using (_≡_ ; module ≡-Reasoning)
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_×_ ; _,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Vec hiding ([_])

open import Notations
open import Data.Nat.Primality



module Examples.Groups.Pauli.Semantics (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime


Pauli1 = ℤ ₚ × ℤ ₚ

Pauli : ℕ → Set
Pauli n = Vec Pauli1 n

sform1 : Pauli1 → Pauli1 → ℤ ₚ
sform1 (a , b) (c , d) = (- a) * d + c * b

sform : ∀ {n} → Pauli n → Pauli n → ℤ ₚ
sform {₀} [] [] = ₀
sform {₁₊ n} (x ∷ ps) (y ∷ qs) = sform1 x y + sform ps qs


cong₃ : ∀ {A B C D : Set}(f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a  ≡ f y v b
cong₃ f Eq.refl Eq.refl Eq.refl = Eq.refl


pIₙ : ∀ {n} → Pauli n
pIₙ {₀} = []
pIₙ {₁₊ n} = (₀ , ₀) ∷ pIₙ {n}

pZ : Pauli1
pZ = (₀ , ₁)

pX : Pauli1
pX = (₁ , ₀)

pI : Pauli1
pI = (₀ , ₀)

pZₙ : ∀ {n} → Pauli n
pZₙ {₀} = []
pZₙ {₁} = pZ ∷ []
pZₙ {₁₊ n} = pI ∷ pZₙ

pXₙ : ∀ {n} → Pauli n
pXₙ {₀} = []
pXₙ {₁} = pX ∷ []
pXₙ {₁₊ n} = pI ∷ pXₙ

pX₀ : ∀ {n} → Pauli n
pX₀ {₀} = []
pX₀ {₁₊ n} = pX ∷ pIₙ

pZ₀ : ∀ {n} → Pauli n
pZ₀ {₀} = []
pZ₀ {₁₊ n} = pZ ∷ pIₙ

pX₀Z₀ : ∀ {n} (e : ℤ ₚ) → Pauli n
pX₀Z₀ {₀} e = []
pX₀Z₀ {₁₊ n} e = (₁ , e) ∷ pIₙ

pXₙZₙ : ∀ {n} (e : ℤ ₚ) → Pauli n
pXₙZₙ {₀} e = []
pXₙZₙ {₁} e = (₁ , e) ∷ []
pXₙZₙ {₁₊ n} e = pI ∷ pXₙZₙ e

pXZ : ∀ (e : ℤ ₚ) → Pauli1
pXZ e = (₁ , e)


open import Algebra.Properties.Ring (+-*-ring p-2)

sform1-antisym : ∀ (p q : Pauli1) -> sform1 p q ≡ - sform1 q p
sform1-antisym p@(a , b) q@(c , d) = begin
  sform1 (a , b) (c , d) ≡⟨ auto ⟩
  (- a) * d + c * b ≡⟨ +-comm (- a * d) (c * b) ⟩
  (c * b) + - a * d ≡⟨ Eq.cong (_+ - a * d) (Eq.cong (_* b) (Eq.sym (-‿involutive c))) ⟩
  (- - c * b) + - a * d ≡⟨ Eq.cong₂ _+_ (Eq.sym (-‿distribˡ-* (- c) b)) (Eq.sym (-‿distribˡ-* a d)) ⟩
  - (- c * b) + - (a * d) ≡⟨ (-‿+-comm (- c * b) (a * d)) ⟩
  - ((- c) * b + a * d) ≡⟨ auto ⟩
  - sform1 (c , d) (a , b) ∎
  where
  open ≡-Reasoning

sform-antisym1 : ∀ (p q : Pauli 1) -> sform p q ≡ - sform q p
sform-antisym1 p@((a , b) ∷ []) q@((c , d) ∷ []) = begin
  sform1 (a , b) (c , d) + ₀ ≡⟨ +-identityʳ (sform1 (a , b) (c , d)) ⟩
  sform1 (a , b) (c , d) ≡⟨ sform1-antisym (a , b) (c , d) ⟩
  - sform1 (c , d) (a , b) ≡⟨ Eq.cong -_ (Eq.sym (+-identityʳ (sform1 (c , d) (a , b)))) ⟩
  - (sform1 (c , d) (a , b) + ₀) ∎
  where
  open ≡-Reasoning


infixl 7 _+₁_ _+ₚ_
infixl 8 _*₁_ _*ₚ_
infix 9 -₁_ -ₚ_

_+₁_ : ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
_+₁_ (a , b) (c , d) = (a + c , b + d)

-₁_ : ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
-₁_ (a , b) = (- a , - b)

_*₁_ : ℤ ₚ → ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
_*₁_ a (c , d) = (a * c , a * d)

-ₚ_ : ∀ {n} → Pauli n → Pauli n
-ₚ_ {n} = map -₁_ 

_+ₚ_ : ∀ {n} → Pauli n → Pauli n → Pauli n
_+ₚ_ {n} = zipWith _+₁_ 

_*ₚ_ : ∀ {n} → ℤ ₚ → Pauli n → Pauli n
_*ₚ_ {n} k = map (k *₁_)


------------------------------------------------------------------------
-- (Pauli n , _+ₚ_) is an abelian group
--
-- Pauli n is the n-fold direct power of ℤ/pℤ × ℤ/pℤ, so the group laws
-- reduce, componentwise and coordinatewise, to those of ℤ/pℤ (which live
-- in Zp.ModularArithmetic).

open import Algebra.Structures using (IsAbelianGroup)
open import Algebra.Bundles   using (AbelianGroup ; Group)
open import Level using (0ℓ)

------------------------------------------------------------------------
-- One-qupit (pair) laws, componentwise from ℤ/pℤ

+₁-assoc : ∀ (p q r : Pauli1) → (p +₁ q) +₁ r ≡ p +₁ (q +₁ r)
+₁-assoc (a , b) (c , d) (e , f) = Eq.cong₂ _,_ (+-assoc a c e) (+-assoc b d f)

+₁-identityˡ : ∀ (p : Pauli1) → pI +₁ p ≡ p
+₁-identityˡ (a , b) = Eq.cong₂ _,_ (+-identityˡ a) (+-identityˡ b)

+₁-inverseˡ : ∀ (p : Pauli1) → (-₁ p) +₁ p ≡ pI
+₁-inverseˡ (a , b) = Eq.cong₂ _,_ (+-inverseˡ a) (+-inverseˡ b)

+₁-comm : ∀ (p q : Pauli1) → p +₁ q ≡ q +₁ p
+₁-comm (a , b) (c , d) = Eq.cong₂ _,_ (+-comm a c) (+-comm b d)

------------------------------------------------------------------------
-- n-qupit laws, by induction on the coordinate vector

+ₚ-assoc : ∀ {n} (p q r : Pauli n) → (p +ₚ q) +ₚ r ≡ p +ₚ (q +ₚ r)
+ₚ-assoc []       []       []       = Eq.refl
+ₚ-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  Eq.cong₂ _∷_ (+₁-assoc x y z) (+ₚ-assoc xs ys zs)

+ₚ-identityˡ : ∀ {n} (p : Pauli n) → pIₙ +ₚ p ≡ p
+ₚ-identityˡ []       = Eq.refl
+ₚ-identityˡ (x ∷ xs) = Eq.cong₂ _∷_ (+₁-identityˡ x) (+ₚ-identityˡ xs)

+ₚ-inverseˡ : ∀ {n} (p : Pauli n) → (-ₚ p) +ₚ p ≡ pIₙ
+ₚ-inverseˡ []       = Eq.refl
+ₚ-inverseˡ (x ∷ xs) = Eq.cong₂ _∷_ (+₁-inverseˡ x) (+ₚ-inverseˡ xs)

+ₚ-comm : ∀ {n} (p q : Pauli n) → p +ₚ q ≡ q +ₚ p
+ₚ-comm []       []       = Eq.refl
+ₚ-comm (x ∷ xs) (y ∷ ys) = Eq.cong₂ _∷_ (+₁-comm x y) (+ₚ-comm xs ys)

-- Right-handed identity and inverse, from the left-handed ones by
-- commutativity.
+ₚ-identityʳ : ∀ {n} (p : Pauli n) → p +ₚ pIₙ ≡ p
+ₚ-identityʳ p = Eq.trans (+ₚ-comm p pIₙ) (+ₚ-identityˡ p)

+ₚ-inverseʳ : ∀ {n} (p : Pauli n) → p +ₚ (-ₚ p) ≡ pIₙ
+ₚ-inverseʳ p = Eq.trans (+ₚ-comm p (-ₚ p)) (+ₚ-inverseˡ p)

------------------------------------------------------------------------
-- The abelian-group structure and bundle

+ₚ-isAbelianGroup : ∀ {n} → IsAbelianGroup (_≡_ {A = Pauli n}) _+ₚ_ pIₙ -ₚ_
+ₚ-isAbelianGroup = record
  { isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong        = Eq.cong₂ _+ₚ_
          }
        ; assoc = +ₚ-assoc
        }
      ; identity = +ₚ-identityˡ , +ₚ-identityʳ
      }
    ; inverse = +ₚ-inverseˡ , +ₚ-inverseʳ
    ; ⁻¹-cong = Eq.cong -ₚ_
    }
  ; comm = +ₚ-comm
  }

+ₚ-abelianGroup : ℕ → AbelianGroup 0ℓ 0ℓ
+ₚ-abelianGroup n = record { isAbelianGroup = +ₚ-isAbelianGroup {n} }

+ₚ-group : ℕ → Group 0ℓ 0ℓ
+ₚ-group n = record { isGroup = IsAbelianGroup.isGroup (+ₚ-isAbelianGroup {n}) }


------------------------------------------------------------------------
-- Pauli n is isomorphic to the n-fold direct power of ℤ/pℤ × ℤ/pℤ
--
-- The n-fold power is built by iterating the binary direct product
-- (stdlib Algebra.Construct.DirectProduct), bottoming out at the trivial
-- group.  The isomorphism just reassociates the coordinate vector into
-- the nested product, coordinate by coordinate.

import Algebra.Construct.DirectProduct as ADP
import Algebra.Construct.Terminal as Terminal
open import Algebra.Morphism.Structures using (module GroupMorphisms ; module MonoidMorphisms)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Data.Unit.Polymorphic using (tt)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

private
  -- ℤ/pℤ as a group and H = ℤ/pℤ × ℤ/pℤ (whose carrier is Pauli1 and
  -- whose operation is, definitionally, _+₁_).
  ℤₚ-group : Group 0ℓ 0ℓ
  ℤₚ-group = +-0-group p-2

  H-group : Group 0ℓ 0ℓ
  H-group = ADP.group ℤₚ-group ℤₚ-group

-- The n-fold direct power of H.
pow : ℕ → Group 0ℓ 0ℓ
pow zero    = Terminal.group
pow (suc n) = ADP.group H-group (pow n)

-- Reassociate the coordinate vector into the nested product and back.
-- (n is kept explicit: pow is not injective, so it can't be recovered
-- from the power's carrier by unification.)
to : (n : ℕ) → Pauli n → Group.Carrier (pow n)
to zero    []       = tt
to (suc n) (x ∷ xs) = x , to n xs

from : (n : ℕ) → Group.Carrier (pow n) → Pauli n
from zero    _       = []
from (suc n) (x , r) = x ∷ from n r

-- The two round-trips.
from∘to : (n : ℕ) (p : Pauli n) → from n (to n p) ≡ p
from∘to zero    []       = Eq.refl
from∘to (suc n) (x ∷ xs) = Eq.cong (x ∷_) (from∘to n xs)

to∘from : (n : ℕ) (c : Group.Carrier (pow n)) → Group._≈_ (pow n) (to n (from n c)) c
to∘from zero    c       = tt
to∘from (suc n) (x , r) = Group.refl H-group , to∘from n r

-- from reflects the (pointwise) equality of the power into ≡.
from-cong : (n : ℕ) {c c' : Group.Carrier (pow n)}
          → Group._≈_ (pow n) c c' → from n c ≡ from n c'
from-cong zero                          eq          = Eq.refl
from-cong (suc n) {x , r} {x' , r'} (xeq , req) = Eq.cong₂ _∷_ (≡×≡⇒≡ xeq) (from-cong n req)

-- to is a group homomorphism.
to-cong : (n : ℕ) {p q : Pauli n} → p ≡ q → Group._≈_ (pow n) (to n p) (to n q)
to-cong n Eq.refl = Group.refl (pow n)

to-homo : (n : ℕ) (p q : Pauli n)
        → Group._≈_ (pow n) (to n (p +ₚ q)) (Group._∙_ (pow n) (to n p) (to n q))
to-homo zero    []       []       = tt
to-homo (suc n) (x ∷ xs) (y ∷ ys) = Group.refl H-group , to-homo n xs ys

to-ε : (n : ℕ) → Group._≈_ (pow n) (to n (pIₙ {n})) (Group.ε (pow n))
to-ε zero    = tt
to-ε (suc n) = Group.refl H-group , to-ε n

-- The group isomorphism, for each n.
module _ (n : ℕ) where
  open MonoidMorphisms (Group.rawMonoid (+ₚ-group n)) (Group.rawMonoid (pow n))
    using (IsMonoidHomomorphism)
  open GroupMorphisms (Group.rawGroup (+ₚ-group n)) (Group.rawGroup (pow n))
    using (IsGroupIsomorphism)

  toMonoidHomo : IsMonoidHomomorphism (to n)
  toMonoidHomo = record
    { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = to-cong n }
        ; homo              = to-homo n
        }
    ; ε-homo = to-ε n
    }

  Pauli≅pow : IsGroupIsomorphism (to n)
  Pauli≅pow = record
    { isGroupMonomorphism = record
        { isGroupHomomorphism =
            isMonoidHomomorphism⇒isGroupHomomorphism (+ₚ-group n) (pow n) toMonoidHomo
        ; injective = λ {p} {q} eq →
            Eq.trans (Eq.sym (from∘to n p)) (Eq.trans (from-cong n eq) (from∘to n q))
        }
    ; surjective = λ c → from n c , λ {z} eq → Group.trans (pow n) (to-cong n eq) (to∘from n c)
    }


------------------------------------------------------------------------
-- Pauli1 (with _+₁_) is isomorphic to the direct product ℤ/pℤ × ℤ/pℤ
--
-- Pauli1 *is* the carrier ℤ/pℤ × ℤ/pℤ and _+₁_ *is* the product
-- operation (definitionally, via ×-eta), so the identity map is the
-- isomorphism; the only content is the change of equality — ≡ on Pauli1
-- versus the pointwise equality of the product.

+₁-identityʳ : ∀ (p : Pauli1) → p +₁ pI ≡ p
+₁-identityʳ p = Eq.trans (+₁-comm p pI) (+₁-identityˡ p)

+₁-inverseʳ : ∀ (p : Pauli1) → p +₁ (-₁ p) ≡ pI
+₁-inverseʳ p = Eq.trans (+₁-comm p (-₁ p)) (+₁-inverseˡ p)

+₁-isAbelianGroup : IsAbelianGroup (_≡_ {A = Pauli1}) _+₁_ pI -₁_
+₁-isAbelianGroup = record
  { isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong        = Eq.cong₂ _+₁_
          }
        ; assoc = +₁-assoc
        }
      ; identity = +₁-identityˡ , +₁-identityʳ
      }
    ; inverse = +₁-inverseˡ , +₁-inverseʳ
    ; ⁻¹-cong = Eq.cong -₁_
    }
  ; comm = +₁-comm
  }

+₁-group : Group 0ℓ 0ℓ
+₁-group = record { isGroup = IsAbelianGroup.isGroup +₁-isAbelianGroup }

module _ where
  open MonoidMorphisms (Group.rawMonoid +₁-group) (Group.rawMonoid H-group)
    using (IsMonoidHomomorphism)
  open GroupMorphisms (Group.rawGroup +₁-group) (Group.rawGroup H-group)
    using (IsGroupIsomorphism)

  -- The identity on ℤ/pℤ × ℤ/pℤ.
  idₚ : Pauli1 → Pauli1
  idₚ p = p

  idₚ-monoidHomo : IsMonoidHomomorphism idₚ
  idₚ-monoidHomo = record
    { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = Group.reflexive H-group }
        ; homo              = λ p q → Group.refl H-group
        }
    ; ε-homo = Group.refl H-group
    }

  Pauli1≅ℤₚ×ℤₚ : IsGroupIsomorphism idₚ
  Pauli1≅ℤₚ×ℤₚ = record
    { isGroupMonomorphism = record
        { isGroupHomomorphism =
            isMonoidHomomorphism⇒isGroupHomomorphism +₁-group H-group idₚ-monoidHomo
        ; injective = λ e → ≡×≡⇒≡ e
        }
    ; surjective = λ y → y , λ {z} z≡y → Group.reflexive H-group z≡y
    }


