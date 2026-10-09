------------------------------------------------------------------------
-- Presentations of groups
--
-- First consequences of the relations of Figure 6: every generator is
-- an involution, so words have inverses and cancel; conjugation by
-- X_[a,b]; and words with disjoint indices commute.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; ≢-sym)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  variable
    a b : Fin n

------------------------------------------------------------------------
-- Involutions and inverses

Z-Z : Z a • Z a ≈ ε
Z-Z = axiom a1

X-X : .(p : a < b) → X a b p • X a b p ≈ ε
X-X p = axiom (a2 p)

H-H : .(p : a < b) → H a b p • H a b p ≈ ε
H-H p = axiom (a3 p)

-- Every generator is an involution.
gen-gen : (g : Gen n) → [ g ]ʷ • [ g ]ʷ ≈ ε
gen-gen (X-gen a b p) = X-X p
gen-gen (H-gen a b p) = H-H p
gen-gen (Z-gen a)     = Z-Z

grouplike : Grouplike (_===_ {n})
grouplike g = [ g ]ʷ , gen-gen g

open Group-Lemmas (_===_ {n}) grouplike public
  using (_⁻¹ ; inverseˡ ; inverseʳ ; •-cancelˡ ; •-cancelʳ ; ⁻¹-cong)

------------------------------------------------------------------------
-- Conjugation by X

-- A X = X B gives B X = X A.
flip-X : ∀ {A B : Word (Gen n)} .(p : a < b) →
         A • X a b p ≈ X a b p • B → B • X a b p ≈ X a b p • A
flip-X {A = A} {B} p h = begin
  B • X′                        ≈⟨ sym left-unit ⟩
  ε • B • X′                    ≈⟨ cleft sym (X-X p) ⟩
  (X′ • X′) • B • X′            ≈⟨ assoc ⟩
  X′ • X′ • B • X′              ≈⟨ cright sym assoc ⟩
  X′ • (X′ • B) • X′            ≈⟨ cright cleft sym h ⟩
  X′ • (A • X′) • X′            ≈⟨ cright assoc ⟩
  X′ • A • (X′ • X′)            ≈⟨ cright cright X-X p ⟩
  X′ • A • ε                    ≈⟨ cright right-unit ⟩
  X′ • A                        ∎
  where X′ = X _ _ p

-- A X = X B gives B = X A X.
conj-X : ∀ {A B : Word (Gen n)} .(p : a < b) → A • X a b p ≈ X a b p • B → B ≈ X a b p • A • X a b p
conj-X {A = A} {B} p h = begin
  B                       ≈⟨ sym left-unit ⟩
  ε • B                   ≈⟨ cleft sym (X-X p) ⟩
  (X′ • X′) • B           ≈⟨ assoc ⟩
  X′ • (X′ • B)           ≈⟨ cright sym h ⟩
  X′ • (A • X′)           ∎
  where X′ = X _ _ p

-- A X = X B gives A = X B X.
conj-X′ : ∀ {A B : Word (Gen n)} .(p : a < b) → A • X a b p ≈ X a b p • B → A ≈ X a b p • B • X a b p
conj-X′ {A = A} {B} p h = begin
  A                       ≈⟨ sym right-unit ⟩
  A • ε                   ≈⟨ cright sym (X-X p) ⟩
  A • (X′ • X′)           ≈⟨ sym assoc ⟩
  (A • X′) • X′           ≈⟨ cleft h ⟩
  (X′ • B) • X′           ≈⟨ assoc ⟩
  X′ • B • X′             ∎
  where X′ = X _ _ p

------------------------------------------------------------------------
-- Generators with disjoint indices commute ((b1)–(b6)), and so do words

-- The indices a generator acts on.
idx : Gen n → List (Fin n)
idx (X-gen a b _) = a ∷ b ∷ []
idx (H-gen a b _) = a ∷ b ∷ []
idx (Z-gen a)     = a ∷ []

Apart : Gen n → Gen n → Set
Apart g h = All (λ x → All (x ≢_) (idx h)) (idx g)

comm-gen : (g h : Gen n) → Apart g h → [ g ]ʷ • [ h ]ʷ ≈ [ h ]ʷ • [ g ]ʷ
comm-gen (Z-gen a) (Z-gen c) ((ac ∷ []) ∷ []) = axiom (b1 ac)
comm-gen (Z-gen a) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ []) = axiom (b2 q ac ad)
comm-gen (Z-gen a) (H-gen c d q) ((ac ∷ ad ∷ []) ∷ []) = axiom (b4 q ac ad)
comm-gen (X-gen a b p) (Z-gen c) ((ac ∷ []) ∷ (bc ∷ []) ∷ []) =
  sym (axiom (b2 p (≢-sym ac) (≢-sym bc)))
comm-gen (X-gen a b p) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (b3 p q ac ad bc bd)
comm-gen (X-gen a b p) (H-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (b5 p q ac ad bc bd)
comm-gen (H-gen a b p) (Z-gen c) ((ac ∷ []) ∷ (bc ∷ []) ∷ []) =
  sym (axiom (b4 p (≢-sym ac) (≢-sym bc)))
comm-gen (H-gen a b p) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  sym (axiom (b5 q p (≢-sym ac) (≢-sym bc) (≢-sym ad) (≢-sym bd)))
comm-gen (H-gen a b p) (H-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (b6 p q ac ad bc bd)

-- Every letter of u is apart from h.
Apartʷ : Word (Gen n) → Gen n → Set
Apartʷ [ g ]ʷ h = Apart g h
Apartʷ ε h = ⊤
Apartʷ (u • v) h = Apartʷ u h × Apartʷ v h

comm-word : (u : Word (Gen n)) (h : Gen n) → Apartʷ u h → u • [ h ]ʷ ≈ [ h ]ʷ • u
comm-word [ g ]ʷ h ap = comm-gen g h ap
comm-word ε h _ = trans left-unit (sym right-unit)
comm-word (u • v) h (au , av) = begin
  (u • v) • [ h ]ʷ      ≈⟨ assoc ⟩
  u • (v • [ h ]ʷ)      ≈⟨ cright comm-word v h av ⟩
  u • ([ h ]ʷ • v)      ≈⟨ sym assoc ⟩
  (u • [ h ]ʷ) • v      ≈⟨ cleft comm-word u h au ⟩
  ([ h ]ʷ • u) • v      ≈⟨ assoc ⟩
  [ h ]ʷ • (u • v)      ∎

-- Every letter of u is apart from every letter of v.
Apartʷʷ : Word (Gen n) → Word (Gen n) → Set
Apartʷʷ u [ h ]ʷ = Apartʷ u h
Apartʷʷ u ε = ⊤
Apartʷʷ u (v • v′) = Apartʷʷ u v × Apartʷʷ u v′

comm-words : (u v : Word (Gen n)) → Apartʷʷ u v → u • v ≈ v • u
comm-words u [ h ]ʷ ap = comm-word u h ap
comm-words u ε _ = trans right-unit (sym left-unit)
comm-words u (v • v′) (a , a′) = begin
  u • (v • v′)          ≈⟨ sym assoc ⟩
  (u • v) • v′          ≈⟨ cleft comm-words u v a ⟩
  (v • u) • v′          ≈⟨ assoc ⟩
  v • (u • v′)          ≈⟨ cright comm-words u v′ a′ ⟩
  v • (v′ • u)          ≈⟨ sym assoc ⟩
  (v • v′) • u          ∎
