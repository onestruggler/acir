------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators on n qubits, indexed by bit vectors, over any carrier with
-- an addition and a multiplication
--
-- The definitions only: sums over bit vectors, the product of
-- operators, the identity, scalars, the Kronecker product, and the
-- tries that store an operator as data so that a long product is
-- computed once (after Clifford.Qubit.Model.Algebra, which has them over
-- ℤ/17ℤ).  Semantics.Laws proves the laws over a commutative ring;
-- Semantics.Interpretation also runs the definitions on ℤ, where the
-- relations are checked by evaluation.
--
-- A basis vector is a bit vector, wire 0 first.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Semantics.Ops
  (C : Set) (_+_ _*_ : C → C → C) (0c 1c : C)
  where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
  variable
    k l m n : ℕ

------------------------------------------------------------------------
-- Bit vectors and sums

Bits : ℕ → Set
Bits n = Vec Bool n

δb : Bits n → Bits n → C
δb []           []           = 1c
δb (true  ∷ xs) (true  ∷ ys) = δb xs ys
δb (false ∷ xs) (false ∷ ys) = δb xs ys
δb (true  ∷ _)  (false ∷ _)  = 0c
δb (false ∷ _)  (true  ∷ _)  = 0c

-- Sum over all 2ⁿ bit vectors.
Σb : (Bits n → C) → C
Σb {zero}  f = f []
Σb {suc n} f = Σb (λ bs → f (false ∷ bs)) + Σb (λ bs → f (true ∷ bs))

------------------------------------------------------------------------
-- Operators

infixl 7 _⊙_

Op : ℕ → Set
Op n = Bits n → Bits n → C

_⊙_ : Op n → Op n → Op n
(M ⊙ N) x y = Σb (λ z → M x z * N z y)

Idₒ : Op n
Idₒ = δb

scal : C → Op n
scal c x y = c * δb x y

-- M acts on the first m wires, N on the rest.
tensor : Op m → Op n → Op (m +ℕ n)
tensor {zero}  M N x       y       = M [] [] * N x y
tensor {suc m} M N (a ∷ x) (b ∷ y) = tensor (λ u v → M (a ∷ u) (b ∷ v)) N x y

------------------------------------------------------------------------
-- Matrices as tries

Tab : ℕ → Set → Set
Tab zero    A = A
Tab (suc k) A = Tab k A × Tab k A

tab : (k : ℕ) {A : Set} → (Bits k → A) → Tab k A
tab zero    f = f []
tab (suc k) f = tab k (λ bs → f (false ∷ bs)) , tab k (λ bs → f (true ∷ bs))

get : {A : Set} → Tab k A → Bits k → A
get {k = zero}  t       []           = t
get {k = suc k} (l , r) (false ∷ bs) = get l bs
get {k = suc k} (l , r) (true  ∷ bs) = get r bs

get-tab : (k : ℕ) {A : Set} (f : Bits k → A) (x : Bits k) → get (tab k f) x ≡ f x
get-tab zero    f []           = Eq.refl
get-tab (suc k) f (false ∷ bs) = get-tab k (λ cs → f (false ∷ cs)) bs
get-tab (suc k) f (true  ∷ bs) = get-tab k (λ cs → f (true ∷ cs)) bs

-- Wrapped in a record so that the width is inferable.
record Mat (k : ℕ) : Set where
  constructor mat
  field entries : Tab k (Tab k C)

open Mat public

ix : Mat k → Op k
ix M x y = get (get (entries M) x) y

matOf : Op k → Mat k
matOf {k} M = mat (tab k (λ x → tab k (λ y → M x y)))

ix-matOf : (M : Op k) → ∀ x y → ix (matOf M) x y ≡ M x y
ix-matOf {k} M x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-tab k (λ u → tab k (λ v → M u v)) x))
           (get-tab k (λ v → M x v) y)

mulM : Mat k → Mat k → Mat k
mulM M N = matOf (ix M ⊙ ix N)

idM : Mat k
idM = matOf Idₒ

tenM : Mat k → Mat l → Mat (k +ℕ l)
tenM M N = matOf (tensor (ix M) (ix N))

scalM : C → Mat k
scalM c = matOf (scal c)
