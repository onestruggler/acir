------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of CNOT-dihedral circuits: the phase polynomial
-- representation (Definition 3.5)
--
-- A CNOT-dihedral operator sends a basis state to a basis state up to
-- a power of ω,
--
--     W |x⟩ = ω^(p x) |f x⟩,
--
-- so it is the pair of a function f on bit vectors and a phase p with
-- values in ℤ₈ — a monomial matrix, kept as the function
-- x ↦ (f x , p x).  Composition is composition of the functions with
-- the phases added along the way; no sums over intermediate indices
-- ever arise, which is what makes this semantics cheap to compute and
-- to compare.  Operators are compared pointwise (_≐_), and an operator
-- on k wires is stored as a table over its 2ᵏ inputs (Mat), where the
-- relations are checked by `refl`.
--
-- Wire 0 is the bottom wire and comes first in a bit vector.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT-Dihedral.Semantics where

open import Algebra.Bundles using (Monoid)
open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; _++_)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Data.Bool.Properties as BoolP
import Data.Product.Properties as ProdP
import Data.Vec.Properties as VecP

open import Notations using (₀ ; ₁₊ ; ₂₊)

open import Examples.Groups.CNOT-Dihedral.Semantics.Z8 public

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- Operators

Bits : ℕ → Set
Bits n = Vec Bool n

-- x ↦ (f x , p x).
Op : ℕ → Set
Op n = Bits n → Bits n × ℤ₈

Idₒ : Op n
Idₒ x = x , 0₈

-- Sequential composition, M first.
infixr 7 _⊙_

_⊙_ : Op n → Op n → Op n
(M ⊙ N) x = proj₁ (N (proj₁ (M x))) , proj₂ (M x) + proj₂ (N (proj₁ (M x)))

-- Pointwise equality.
infix 4 _≐_

_≐_ : Op n → Op n → Set
M ≐ N = ∀ x → M x ≡ N x

≐-refl : (M : Op n) → M ≐ M
≐-refl M x = Eq.refl

≐-sym : {M N : Op n} → M ≐ N → N ≐ M
≐-sym e x = Eq.sym (e x)

≐-trans : {M N P : Op n} → M ≐ N → N ≐ P → M ≐ P
≐-trans e f x = Eq.trans (e x) (f x)

⊙-cong : {M M' N N' : Op n} → M ≐ M' → N ≐ N' → (M ⊙ N) ≐ (M' ⊙ N')
⊙-cong {M = M} {M'} {N} {N'} e f x
  rewrite e x | f (proj₁ (M' x)) = Eq.refl

⊙-assoc : (M N P : Op n) → ((M ⊙ N) ⊙ P) ≐ (M ⊙ (N ⊙ P))
⊙-assoc M N P x = Eq.cong₂ _,_ Eq.refl
  (+-assoc (proj₂ (M x)) (proj₂ (N (proj₁ (M x)))) _)

⊙-identityˡ : (M : Op n) → (Idₒ ⊙ M) ≐ M
⊙-identityˡ M x = Eq.cong₂ _,_ Eq.refl (+-identityˡ (proj₂ (M x)))

⊙-identityʳ : (M : Op n) → (M ⊙ Idₒ) ≐ M
⊙-identityʳ M x = Eq.cong₂ _,_ Eq.refl (+-identityʳ (proj₂ (M x)))

-- The monoid of operators on n wires, under pointwise equality.
Op-monoid : ℕ → Monoid 0ℓ 0ℓ
Op-monoid n = record
  { Carrier = Op n
  ; _≈_     = _≐_
  ; _∙_     = _⊙_
  ; ε       = Idₒ
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = record
          { refl  = λ {M} → ≐-refl M
          ; sym   = λ {M} {N} → ≐-sym {M = M} {N}
          ; trans = λ {M} {N} {P} → ≐-trans {M = M} {N} {P} }
        ; ∙-cong = λ {M} {M'} {N} {N'} → ⊙-cong {M = M} {M'} {N} {N'} }
      ; assoc = ⊙-assoc }
    ; identity = ⊙-identityˡ , ⊙-identityʳ }
  }

------------------------------------------------------------------------
-- The gates

-- The scalar: a phase on every input.
ωₒ : Op n
ωₒ x = x , 1₈

-- On wire 0.
Xₒ Tₒ : Op (₁₊ n)
Xₒ (a ∷ x) = not a ∷ x , 0₈
Tₒ (a ∷ x) = a ∷ x , (if a then 1₈ else 0₈)

-- On wires 0 and 1: CNOT's control is wire 1, its target wire 0.
CNOTₒ SWAPₒ : Op (₂₊ n)
CNOTₒ (t ∷ c ∷ x) = (c xor t) ∷ c ∷ x , 0₈
SWAPₒ (a ∷ b ∷ x) = b ∷ a ∷ x , 0₈

------------------------------------------------------------------------
-- Shifting an operator up a wire, and embedding one on the bottom wires

up : Op n → Op (₁₊ n)
up M (a ∷ x) = a ∷ proj₁ (M x) , proj₂ (M x)

up-cong : {M N : Op n} → M ≐ N → up M ≐ up N
up-cong e (a ∷ x) rewrite e x = Eq.refl

up-⊙ : (M N : Op n) → up (M ⊙ N) ≐ (up M ⊙ up N)
up-⊙ M N (a ∷ x) = Eq.refl

up-Id : up (Idₒ {n}) ≐ Idₒ
up-Id (a ∷ x) = Eq.refl

-- The bottom k bits and the rest.
split : (k : ℕ) → Bits (k +ℕ n) → Bits k × Bits n
split zero    x       = [] , x
split (suc k) (a ∷ x) = a ∷ proj₁ (split k x) , proj₂ (split k x)

split-++ : (u : Bits k) (v : Bits n) → split k (u ++ v) ≡ (u , v)
split-++ []      v = Eq.refl
split-++ (a ∷ u) v rewrite split-++ u v = Eq.refl

++-split : (x : Bits (k +ℕ n)) → proj₁ (split k x) ++ proj₂ (split k x) ≡ x
++-split {zero}  x       = Eq.refl
++-split {suc k} (a ∷ x) = Eq.cong (a ∷_) (++-split {k} x)

-- An operator on k wires acting on the bottom k of k + n wires.
emb : Op k → Op (k +ℕ n)
emb {k} M x =
  proj₁ (M (proj₁ (split k x))) ++ proj₂ (split k x) , proj₂ (M (proj₁ (split k x)))

emb-cong : {M N : Op k} → M ≐ N → emb {k} {n} M ≐ emb N
emb-cong {k} e x rewrite e (proj₁ (split k x)) = Eq.refl

emb-id : emb {k} {n} Idₒ ≐ Idₒ
emb-id {k} {n} x = Eq.cong (_, 0₈) (++-split {k} {n} x)

emb-⊙ : (M N : Op k) → emb {k} {n} (M ⊙ N) ≐ (emb M ⊙ emb N)
emb-⊙ {k} M N x
  rewrite split-++ (proj₁ (M (proj₁ (split k x)))) (proj₂ (split k x)) = Eq.refl

emb-up : (M : Op k) → emb {₁₊ k} {n} (up M) ≐ up (emb M)
emb-up M (a ∷ x) = Eq.refl

-- The gates, embedded with more wires above, are themselves.
emb-ω : emb {k} {n} ωₒ ≐ ωₒ
emb-ω {k} {n} x = Eq.cong (_, 1₈) (++-split {k} {n} x)

emb-X : emb {₁₊ k} {n} Xₒ ≐ Xₒ
emb-X {k} {n} (a ∷ x) = Eq.cong (λ y → not a ∷ y , 0₈) (++-split {k} {n} x)

emb-T : emb {₁₊ k} {n} Tₒ ≐ Tₒ
emb-T {k} {n} (a ∷ x) = Eq.cong (λ y → a ∷ y , (if a then 1₈ else 0₈)) (++-split {k} {n} x)

emb-CNOT : emb {₂₊ k} {n} CNOTₒ ≐ CNOTₒ
emb-CNOT {k} {n} (t ∷ c ∷ x) = Eq.cong (λ y → (c xor t) ∷ c ∷ y , 0₈) (++-split {k} {n} x)

emb-SWAP : emb {₂₊ k} {n} SWAPₒ ≐ SWAPₒ
emb-SWAP {k} {n} (a ∷ b ∷ x) = Eq.cong (λ y → b ∷ a ∷ y , 0₈) (++-split {k} {n} x)

------------------------------------------------------------------------
-- Stored operators
--
-- An operator on k wires tabulated over its 2ᵏ inputs; two such tables
-- are compared by `refl`, or decided.

Tab : ℕ → Set → Set
Tab zero    A = A
Tab (suc k) A = Tab k A × Tab k A

tab : (k : ℕ) {A : Set} → (Bits k → A) → Tab k A
tab zero    f = f []
tab (suc k) f = tab k (λ x → f (false ∷ x)) , tab k (λ x → f (true ∷ x))

get : {A : Set} → Tab k A → Bits k → A
get {zero}  t []          = t
get {suc k} t (false ∷ x) = get (proj₁ t) x
get {suc k} t (true ∷ x)  = get (proj₂ t) x

get-tab : (k : ℕ) {A : Set} (f : Bits k → A) (x : Bits k) → get (tab k f) x ≡ f x
get-tab zero    f []          = Eq.refl
get-tab (suc k) f (false ∷ x) = get-tab k _ x
get-tab (suc k) f (true ∷ x)  = get-tab k _ x

tab-dec : (k : ℕ) {A : Set} → DecidableEquality A → DecidableEquality (Tab k A)
tab-dec zero    d = d
tab-dec (suc k) d = ProdP.≡-dec (tab-dec k d) (tab-dec k d)

Mat : ℕ → Set
Mat k = Tab k (Bits k × ℤ₈)

matOf : Op k → Mat k
matOf {k} M = tab k M

ix : Mat k → Op k
ix = get

ix-matOf : (M : Op k) → ix (matOf M) ≐ M
ix-matOf {k} M = get-tab k M

mat-dec : DecidableEquality (Mat k)
mat-dec {k} = tab-dec k (ProdP.≡-dec (VecP.≡-dec BoolP._≟_) _≟₈_)

mulM : Mat k → Mat k → Mat k
mulM A B = matOf (ix A ⊙ ix B)

ix-mul : (A B : Mat k) → ix (mulM A B) ≐ (ix A ⊙ ix B)
ix-mul A B = ix-matOf (ix A ⊙ ix B)

ix-≡ : {A B : Mat k} → A ≡ B → ix A ≐ ix B
ix-≡ {A = A} Eq.refl = ≐-refl (ix A)
