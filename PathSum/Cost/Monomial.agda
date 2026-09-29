------------------------------------------------------------------------
-- Presentations of groups
--
-- Monomials as bit vectors, and the steps on them, in the cost model
-- (for Amy, QPL 2018, proposition 3.2)
--
-- A monomial of PathSum.Polynomial is a pair of bit vectors,
-- Subset n × Subset m, one bit per input and one per path variable.
-- The operations the sparse algorithms perform on monomials are
-- written here as programs in PathSum.Cost's monad, each with the
-- function it computes and a bound on its cost: one step per bit
-- visited.  Comparing two monomials costs at most n + m (eqMonᶜ, whose
-- value is PathSum.Polynomial.Properties._≡ᵐᵇ_); looking up a bit, or
-- clearing one, at most as many as the vector is long; removing a bit
-- (removeAtᶜ, Vec.removeAt) likewise; unions and symmetric differences
-- n + m; degrees (∥_∥) and emptiness (emptyᵐ) n + m.
--
-- The monomials of degree at most d, and the submonomials of degree at
-- most d of a monomial S, are enumerated by Pascal's rule, as
-- PathSum.Size.Monomials.monomials≤ and PathSum.Size.Submonomials.
-- subᵐ≤ define them; the programs here compute exactly those lists
-- (value-subᵐ≤ᶜ, value-monomials≤ᶜ, through monomials≤ ≡ subᵐ≤ ⊤ ⊤),
-- so the counting lemmas of those modules bound their lengths.  The
-- cost of the enumeration is at most 3 (n + m + 2) times the length of
-- the list it produces (cost-subᵐ≤ᶜ): each level of the recursion
-- visits every cell of the lists below it a bounded number of times.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Cost.Monomial where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _∨_; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; inside; outside; ⊥; ⊤; ⁅_⁆; _∪_; _─_; ∣_∣)
  renaming (_-_ to _∖_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Nat.Base using
  (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; removeAt; zipWith; lookup)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Cost
open import PathSum.Linear using (_⊕ᵐ_)
open import PathSum.Polynomial using
  (Mon; Var; x[_]; y[_]; ⟪_⟫; 1ᵐ; ∥_∥; _∪ᵐ_; _∖ᵐ_)
open import PathSum.Polynomial.Properties using
  (_≡ᵇ_; _≡ᵐᵇ_; emptyᵇ; emptyᵐ)
open import PathSum.Size.Monomials using
  (consˣ; subsets≤; monomials≤)
open import PathSum.Size.Submonomials using (subsOf≤; subᵐ≤)

import Data.List.Properties as List
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    A : Set
    k n m : ℕ


------------------------------------------------------------------------
-- Bit vectors

-- Equality, bit by bit, stopping at the first difference.  Its value
-- is _≡ᵇ_, clause for clause.

eqᶜ : Subset k → Subset k → Cost Bool
eqᶜ []            []            = pure true
eqᶜ (inside  ∷ p) (inside  ∷ q) = tick >> eqᶜ p q
eqᶜ (inside  ∷ p) (outside ∷ q) = step false
eqᶜ (outside ∷ p) (inside  ∷ q) = step false
eqᶜ (outside ∷ p) (outside ∷ q) = tick >> eqᶜ p q

value-eqᶜ : (p q : Subset k) → value (eqᶜ p q) ≡ (p ≡ᵇ q)
value-eqᶜ []            []            = refl
value-eqᶜ (inside  ∷ p) (inside  ∷ q) = value-eqᶜ p q
value-eqᶜ (inside  ∷ p) (outside ∷ q) = refl
value-eqᶜ (outside ∷ p) (inside  ∷ q) = refl
value-eqᶜ (outside ∷ p) (outside ∷ q) = value-eqᶜ p q

cost-eqᶜ : (p q : Subset k) → cost (eqᶜ p q) ≤ k
cost-eqᶜ []            []            = z≤n
cost-eqᶜ (inside  ∷ p) (inside  ∷ q) = s≤s (cost-eqᶜ p q)
cost-eqᶜ (inside  ∷ p) (outside ∷ q) = s≤s z≤n
cost-eqᶜ (outside ∷ p) (inside  ∷ q) = s≤s z≤n
cost-eqᶜ (outside ∷ p) (outside ∷ q) = s≤s (cost-eqᶜ p q)

-- Removing the bit at an index, as Vec.removeAt does it.

removeAtᶜ : Vec A (suc k) → Fin (suc k) → Cost (Vec A k)
removeAtᶜ (a ∷ as)          zero    = step as
removeAtᶜ (a ∷ as@(_ ∷ _)) (suc i) = do
  tick
  bs ← removeAtᶜ as i
  pure (a ∷ bs)

value-removeAtᶜ : (as : Vec A (suc k)) (i : Fin (suc k)) →
                  value (removeAtᶜ as i) ≡ removeAt as i
value-removeAtᶜ (a ∷ as)          zero    = refl
value-removeAtᶜ (a ∷ as@(_ ∷ _)) (suc i) =
  cong (a ∷_) (value-removeAtᶜ as i)

cost-removeAtᶜ : (as : Vec A (suc k)) (i : Fin (suc k)) →
                 cost (removeAtᶜ as i) ≤ suc k
cost-removeAtᶜ (a ∷ as)          zero    = s≤s z≤n
cost-removeAtᶜ (a ∷ as@(_ ∷ _)) (suc i) = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (removeAtᶜ as i))))
             (cost-removeAtᶜ as i))

-- Clearing the bit at an index.  Its specification, clear, is the
-- set difference p ∖ i of Data.Fin.Subset, by recursion on the index.

clear : Subset k → Fin k → Subset k
clear (b ∷ p) zero    = outside ∷ p
clear (b ∷ p) (suc i) = b ∷ clear p i

private
  ─-⊥ : (p : Subset k) → p ─ ⊥ ≡ p
  ─-⊥ []      = refl
  ─-⊥ (b ∷ p) = cong (b ∷_) (─-⊥ p)

clear≡∖ : (p : Subset k) (i : Fin k) → clear p i ≡ p ∖ i
clear≡∖ (b ∷ p) zero    = cong (outside ∷_) (sym (─-⊥ p))
clear≡∖ (b ∷ p) (suc i) = cong (b ∷_) (clear≡∖ p i)

clearᶜ : Subset k → Fin k → Cost (Subset k)
clearᶜ (b ∷ p) zero    = step (outside ∷ p)
clearᶜ (b ∷ p) (suc i) = do
  tick
  q ← clearᶜ p i
  pure (b ∷ q)

value-clearᶜ : (p : Subset k) (i : Fin k) → value (clearᶜ p i) ≡ clear p i
value-clearᶜ (b ∷ p) zero    = refl
value-clearᶜ (b ∷ p) (suc i) = cong (b ∷_) (value-clearᶜ p i)

cost-clearᶜ : (p : Subset k) (i : Fin k) → cost (clearᶜ p i) ≤ k
cost-clearᶜ (b ∷ p) zero    = s≤s z≤n
cost-clearᶜ (b ∷ p) (suc i) = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (clearᶜ p i))))
             (cost-clearᶜ p i))

-- Union and symmetric difference, bit by bit.

unionᶜ : Subset k → Subset k → Cost (Subset k)
unionᶜ []      []      = pure []
unionᶜ (a ∷ p) (b ∷ q) = do
  tick
  r ← unionᶜ p q
  pure ((a ∨ b) ∷ r)

value-unionᶜ : (p q : Subset k) → value (unionᶜ p q) ≡ p ∪ q
value-unionᶜ []      []      = refl
value-unionᶜ (a ∷ p) (b ∷ q) = cong ((a ∨ b) ∷_) (value-unionᶜ p q)

cost-unionᶜ : (p q : Subset k) → cost (unionᶜ p q) ≤ k
cost-unionᶜ []      []      = z≤n
cost-unionᶜ (a ∷ p) (b ∷ q) = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (unionᶜ p q))))
             (cost-unionᶜ p q))

xorᶜ : Subset k → Subset k → Cost (Subset k)
xorᶜ []      []      = pure []
xorᶜ (a ∷ p) (b ∷ q) = do
  tick
  r ← xorᶜ p q
  pure ((a xor b) ∷ r)

value-xorᶜ : (p q : Subset k) → value (xorᶜ p q) ≡ zipWith _xor_ p q
value-xorᶜ []      []      = refl
value-xorᶜ (a ∷ p) (b ∷ q) = cong ((a xor b) ∷_) (value-xorᶜ p q)

cost-xorᶜ : (p q : Subset k) → cost (xorᶜ p q) ≤ k
cost-xorᶜ []      []      = z≤n
cost-xorᶜ (a ∷ p) (b ∷ q) = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (xorᶜ p q))))
             (cost-xorᶜ p q))

-- The size of a subset, counting as it goes.

degᶜ : Subset k → Cost ℕ
degᶜ []            = pure 0
degᶜ (inside  ∷ p) = do
  tick
  s ← degᶜ p
  pure (suc s)
degᶜ (outside ∷ p) = tick >> degᶜ p

value-degᶜ : (p : Subset k) → value (degᶜ p) ≡ ∣ p ∣
value-degᶜ []            = refl
value-degᶜ (inside  ∷ p) = cong suc (value-degᶜ p)
value-degᶜ (outside ∷ p) = value-degᶜ p

cost-degᶜ : (p : Subset k) → cost (degᶜ p) ≤ k
cost-degᶜ []            = z≤n
cost-degᶜ (inside  ∷ p) = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (degᶜ p))))
             (cost-degᶜ p))
cost-degᶜ (outside ∷ p) = s≤s (cost-degᶜ p)

-- Whether a subset is empty, stopping at the first element.

emptyᶜ : Subset k → Cost Bool
emptyᶜ []            = pure true
emptyᶜ (inside  ∷ p) = step false
emptyᶜ (outside ∷ p) = tick >> emptyᶜ p

value-emptyᶜ : (p : Subset k) → value (emptyᶜ p) ≡ emptyᵇ p
value-emptyᶜ []            = refl
value-emptyᶜ (inside  ∷ p) = refl
value-emptyᶜ (outside ∷ p) = value-emptyᶜ p

cost-emptyᶜ : (p : Subset k) → cost (emptyᶜ p) ≤ k
cost-emptyᶜ []            = z≤n
cost-emptyᶜ (inside  ∷ p) = s≤s z≤n
cost-emptyᶜ (outside ∷ p) = s≤s (cost-emptyᶜ p)

-- Writing down the empty subset and a singleton.

botᶜ : Cost (Subset k)
botᶜ {k = zero}  = pure []
botᶜ {k = suc k} = do
  tick
  r ← botᶜ
  pure (outside ∷ r)

value-botᶜ : value (botᶜ {k}) ≡ ⊥
value-botᶜ {k = zero}  = refl
value-botᶜ {k = suc k} = cong (outside ∷_) (value-botᶜ {k})

cost-botᶜ : cost (botᶜ {k}) ≤ k
cost-botᶜ {k = zero}  = z≤n
cost-botᶜ {k = suc k} = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (botᶜ {k}))))
             (cost-botᶜ {k}))

singletonᶜ : Fin k → Cost (Subset k)
singletonᶜ zero    = do
  tick
  r ← botᶜ
  pure (inside ∷ r)
singletonᶜ (suc i) = do
  tick
  r ← singletonᶜ i
  pure (outside ∷ r)

value-singletonᶜ : (i : Fin k) → value (singletonᶜ i) ≡ ⁅ i ⁆
value-singletonᶜ {k = suc k} zero    = cong (inside ∷_) (value-botᶜ {k})
value-singletonᶜ             (suc i) = cong (outside ∷_) (value-singletonᶜ i)

cost-singletonᶜ : (i : Fin k) → cost (singletonᶜ i) ≤ k
cost-singletonᶜ {k = suc k} zero    = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (botᶜ {k}))))
             (cost-botᶜ {k}))
cost-singletonᶜ             (suc i) = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (singletonᶜ i))))
             (cost-singletonᶜ i))


------------------------------------------------------------------------
-- Monomials

-- Equality: the input bits, then (only if they agree) the path bits.

private
  value-if-false : (b : Bool) (X : Cost Bool) →
                   value (if b then X else pure false) ≡ b ∧ value X
  value-if-false true  X = refl
  value-if-false false X = refl

  cost-if-false : (b : Bool) (X : Cost Bool) →
                  cost (if b then X else pure false) ≤ cost X
  cost-if-false true  X = ℕ.≤-refl
  cost-if-false false X = z≤n

eqMonᶜ : Mon n m → Mon n m → Cost Bool
eqMonᶜ (α , β) (α′ , β′) = do
  a ← eqᶜ α α′
  if a then eqᶜ β β′ else pure false

value-eqMonᶜ : (γ δ : Mon n m) → value (eqMonᶜ γ δ) ≡ (γ ≡ᵐᵇ δ)
value-eqMonᶜ (α , β) (α′ , β′) = trans
  (value-if-false (value (eqᶜ α α′)) (eqᶜ β β′))
  (cong₂ _∧_ (value-eqᶜ α α′) (value-eqᶜ β β′))

cost-eqMonᶜ : (γ δ : Mon n m) → cost (eqMonᶜ γ δ) ≤ n + m
cost-eqMonᶜ (α , β) (α′ , β′) = ℕ.+-mono-≤ (cost-eqᶜ α α′)
  (ℕ.≤-trans (cost-if-false (value (eqᶜ α α′)) (eqᶜ β β′))
             (cost-eqᶜ β β′))

-- The degree, and whether the monomial is 1.

degᵐᶜ : Mon n m → Cost ℕ
degᵐᶜ (α , β) = do
  a ← degᶜ α
  b ← degᶜ β
  pure (a + b)

value-degᵐᶜ : (γ : Mon n m) → value (degᵐᶜ γ) ≡ ∥ γ ∥
value-degᵐᶜ (α , β) = cong₂ _+_ (value-degᶜ α) (value-degᶜ β)

cost-degᵐᶜ : (γ : Mon n m) → cost (degᵐᶜ γ) ≤ n + m
cost-degᵐᶜ (α , β) = ℕ.+-mono-≤ (cost-degᶜ α)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (degᶜ β))))
             (cost-degᶜ β))

emptyᵐᶜ : Mon n m → Cost Bool
emptyᵐᶜ (α , β) = do
  a ← emptyᶜ α
  if a then emptyᶜ β else pure false

value-emptyᵐᶜ : (γ : Mon n m) → value (emptyᵐᶜ γ) ≡ emptyᵐ γ
value-emptyᵐᶜ (α , β) = trans
  (value-if-false (value (emptyᶜ α)) (emptyᶜ β))
  (cong₂ _∧_ (value-emptyᶜ α) (value-emptyᶜ β))

cost-emptyᵐᶜ : (γ : Mon n m) → cost (emptyᵐᶜ γ) ≤ n + m
cost-emptyᵐᶜ (α , β) = ℕ.+-mono-≤ (cost-emptyᶜ α)
  (ℕ.≤-trans (cost-if-false (value (emptyᶜ α)) (emptyᶜ β))
             (cost-emptyᶜ β))

-- Union and symmetric difference.

unionᵐᶜ : Mon n m → Mon n m → Cost (Mon n m)
unionᵐᶜ (α , β) (α′ , β′) = do
  a ← unionᶜ α α′
  b ← unionᶜ β β′
  pure (a , b)

value-unionᵐᶜ : (γ δ : Mon n m) → value (unionᵐᶜ γ δ) ≡ γ ∪ᵐ δ
value-unionᵐᶜ (α , β) (α′ , β′) =
  cong₂ _,_ (value-unionᶜ α α′) (value-unionᶜ β β′)

cost-unionᵐᶜ : (γ δ : Mon n m) → cost (unionᵐᶜ γ δ) ≤ n + m
cost-unionᵐᶜ (α , β) (α′ , β′) = ℕ.+-mono-≤ (cost-unionᶜ α α′)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (unionᶜ β β′))))
             (cost-unionᶜ β β′))

xorᵐᶜ : Mon n m → Mon n m → Cost (Mon n m)
xorᵐᶜ (α , β) (α′ , β′) = do
  a ← xorᶜ α α′
  b ← xorᶜ β β′
  pure (a , b)

value-xorᵐᶜ : (γ δ : Mon n m) → value (xorᵐᶜ γ δ) ≡ γ ⊕ᵐ δ
value-xorᵐᶜ (α , β) (α′ , β′) =
  cong₂ _,_ (value-xorᶜ α α′) (value-xorᶜ β β′)

cost-xorᵐᶜ : (γ δ : Mon n m) → cost (xorᵐᶜ γ δ) ≤ n + m
cost-xorᵐᶜ (α , β) (α′ , β′) = ℕ.+-mono-≤ (cost-xorᶜ α α′)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (xorᶜ β β′))))
             (cost-xorᶜ β β′))

-- Removing a path variable from a monomial: the monomial S ∖ᵐ y[ i ].

clearʸᶜ : Mon n m → Fin m → Cost (Mon n m)
clearʸᶜ (α , β) i = (λ β′ → α , β′) <$> clearᶜ β i

value-clearʸᶜ : (S : Mon n m) (i : Fin m) →
                value (clearʸᶜ S i) ≡ S ∖ᵐ y[ i ]
value-clearʸᶜ (α , β) i =
  cong (α ,_) (trans (value-clearᶜ β i) (clear≡∖ β i))

cost-clearʸᶜ : (S : Mon n m) (i : Fin m) → cost (clearʸᶜ S i) ≤ m
cost-clearʸᶜ (α , β) i = cost-clearᶜ β i

-- Writing down the monomial 1 and the monomial of a single variable.

oneᶜ : Cost (Mon n m)
oneᶜ = do
  α ← botᶜ
  β ← botᶜ
  pure (α , β)

value-oneᶜ : value (oneᶜ {n} {m}) ≡ 1ᵐ
value-oneᶜ {n} {m} = cong₂ _,_ (value-botᶜ {n}) (value-botᶜ {m})

cost-oneᶜ : cost (oneᶜ {n} {m}) ≤ n + m
cost-oneᶜ {n} {m} = ℕ.+-mono-≤ (cost-botᶜ {n})
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (botᶜ {m}))))
             (cost-botᶜ {m}))

varᶜ : Var n m → Cost (Mon n m)
varᶜ x[ i ] = do
  α ← singletonᶜ i
  β ← botᶜ
  pure (α , β)
varᶜ y[ j ] = do
  α ← botᶜ
  β ← singletonᶜ j
  pure (α , β)

value-varᶜ : (v : Var n m) → value (varᶜ v) ≡ ⟪ v ⟫
value-varᶜ {m = m} x[ i ] =
  cong₂ _,_ (value-singletonᶜ i) (value-botᶜ {m})
value-varᶜ {n = n} y[ j ] =
  cong₂ _,_ (value-botᶜ {n}) (value-singletonᶜ j)

cost-varᶜ : (v : Var n m) → cost (varᶜ v) ≤ n + m
cost-varᶜ {m = m} x[ i ] = ℕ.+-mono-≤ (cost-singletonᶜ i)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (botᶜ {m}))))
             (cost-botᶜ {m}))
cost-varᶜ {n = n} y[ j ] = ℕ.+-mono-≤ (cost-botᶜ {n})
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (singletonᶜ j))))
             (cost-singletonᶜ j))


------------------------------------------------------------------------
-- Enumerating submonomials by Pascal's rule

-- Putting a bit in front of every subset of a list, one step per cell.

consAllᶜ : Bool → List (Subset k) → Cost (List (Subset (suc k)))
consAllᶜ b = mapᶜ (λ s → pure (b ∷ s))

-- The subsets of p of size at most d, clause for clause as
-- PathSum.Size.Submonomials.subsOf≤.

subsOf≤ᶜ : Subset k → ℕ → Cost (List (Subset k))
subsOf≤ᶜ []            d       = step ([] ∷ [])
subsOf≤ᶜ (outside ∷ p) d       = do
  tick
  ss ← subsOf≤ᶜ p d
  consAllᶜ outside ss
subsOf≤ᶜ (inside  ∷ p) zero    = do
  tick
  ss ← subsOf≤ᶜ p zero
  consAllᶜ outside ss
subsOf≤ᶜ (inside  ∷ p) (suc d) = do
  tick
  as  ← subsOf≤ᶜ p d
  bs  ← subsOf≤ᶜ p (suc d)
  as′ ← consAllᶜ inside as
  bs′ ← consAllᶜ outside bs
  appendᶜ as′ bs′

value-subsOf≤ᶜ : (p : Subset k) (d : ℕ) →
                 value (subsOf≤ᶜ p d) ≡ subsOf≤ p d
value-subsOf≤ᶜ []            d       = refl
value-subsOf≤ᶜ (outside ∷ p) d       = trans
  (value-mapᶜ (λ s → pure (outside ∷ s)) (value (subsOf≤ᶜ p d)))
  (cong (map (outside ∷_)) (value-subsOf≤ᶜ p d))
value-subsOf≤ᶜ (inside  ∷ p) zero    = trans
  (value-mapᶜ (λ s → pure (outside ∷ s)) (value (subsOf≤ᶜ p zero)))
  (cong (map (outside ∷_)) (value-subsOf≤ᶜ p zero))
value-subsOf≤ᶜ (inside  ∷ p) (suc d) = trans
  (value-appendᶜ (value (consAllᶜ inside (value (subsOf≤ᶜ p d))))
                 (value (consAllᶜ outside (value (subsOf≤ᶜ p (suc d))))))
  (cong₂ _++_
    (trans (value-mapᶜ (λ s → pure (inside ∷ s)) (value (subsOf≤ᶜ p d)))
           (cong (map (inside ∷_)) (value-subsOf≤ᶜ p d)))
    (trans (value-mapᶜ (λ s → pure (outside ∷ s))
                       (value (subsOf≤ᶜ p (suc d))))
           (cong (map (outside ∷_)) (value-subsOf≤ᶜ p (suc d)))))

-- The submonomials of (α , β) of degree at most d, clause for clause as
-- PathSum.Size.Submonomials.subᵐ≤.

subᵐ≤ᶜ : Subset n → Subset m → ℕ → Cost (List (Mon n m))
subᵐ≤ᶜ []            β d       = do
  ss ← subsOf≤ᶜ β d
  mapᶜ (λ b → pure ([] , b)) ss
subᵐ≤ᶜ (outside ∷ α) β d       = do
  tick
  ss ← subᵐ≤ᶜ α β d
  mapᶜ (λ γ → pure (consˣ outside γ)) ss
subᵐ≤ᶜ (inside  ∷ α) β zero    = do
  tick
  ss ← subᵐ≤ᶜ α β zero
  mapᶜ (λ γ → pure (consˣ outside γ)) ss
subᵐ≤ᶜ (inside  ∷ α) β (suc d) = do
  tick
  as  ← subᵐ≤ᶜ α β d
  bs  ← subᵐ≤ᶜ α β (suc d)
  as′ ← mapᶜ (λ γ → pure (consˣ inside γ)) as
  bs′ ← mapᶜ (λ γ → pure (consˣ outside γ)) bs
  appendᶜ as′ bs′

value-subᵐ≤ᶜ : (α : Subset n) (β : Subset m) (d : ℕ) →
               value (subᵐ≤ᶜ α β d) ≡ subᵐ≤ α β d
value-subᵐ≤ᶜ []            β d       = trans
  (value-mapᶜ (λ b → pure ([] , b)) (value (subsOf≤ᶜ β d)))
  (cong (map (λ b → [] , b)) (value-subsOf≤ᶜ β d))
value-subᵐ≤ᶜ (outside ∷ α) β d       = trans
  (value-mapᶜ (λ γ → pure (consˣ outside γ)) (value (subᵐ≤ᶜ α β d)))
  (cong (map (consˣ outside)) (value-subᵐ≤ᶜ α β d))
value-subᵐ≤ᶜ (inside  ∷ α) β zero    = trans
  (value-mapᶜ (λ γ → pure (consˣ outside γ)) (value (subᵐ≤ᶜ α β zero)))
  (cong (map (consˣ outside)) (value-subᵐ≤ᶜ α β zero))
value-subᵐ≤ᶜ (inside  ∷ α) β (suc d) = trans
  (value-appendᶜ
    (value (mapᶜ (λ γ → pure (consˣ inside γ)) (value (subᵐ≤ᶜ α β d))))
    (value (mapᶜ (λ γ → pure (consˣ outside γ))
                 (value (subᵐ≤ᶜ α β (suc d))))))
  (cong₂ _++_
    (trans (value-mapᶜ (λ γ → pure (consˣ inside γ))
                       (value (subᵐ≤ᶜ α β d)))
           (cong (map (consˣ inside)) (value-subᵐ≤ᶜ α β d)))
    (trans (value-mapᶜ (λ γ → pure (consˣ outside γ))
                       (value (subᵐ≤ᶜ α β (suc d))))
           (cong (map (consˣ outside)) (value-subᵐ≤ᶜ α β (suc d)))))

-- All monomials of degree at most d are the submonomials of the full
-- monomial ⊤ (every variable present).

private
  subsets≡ : ∀ k d → subsOf≤ (⊤ {k}) d ≡ subsets≤ k d
  subsets≡ zero    d       = refl
  subsets≡ (suc k) zero    = cong (map (outside ∷_)) (subsets≡ k zero)
  subsets≡ (suc k) (suc d) = cong₂ _++_
    (cong (map (inside ∷_)) (subsets≡ k d))
    (cong (map (outside ∷_)) (subsets≡ k (suc d)))

monomials≡ : ∀ n m d → subᵐ≤ (⊤ {n}) (⊤ {m}) d ≡ monomials≤ n m d
monomials≡ zero    m d       = cong (map (λ b → [] , b)) (subsets≡ m d)
monomials≡ (suc n) m zero    =
  cong (map (consˣ outside)) (monomials≡ n m zero)
monomials≡ (suc n) m (suc d) = cong₂ _++_
  (cong (map (consˣ inside)) (monomials≡ n m d))
  (cong (map (consˣ outside)) (monomials≡ n m (suc d)))

monomials≤ᶜ : (n m d : ℕ) → Cost (List (Mon n m))
monomials≤ᶜ n m d = subᵐ≤ᶜ (⊤ {n}) (⊤ {m}) d

value-monomials≤ᶜ : ∀ n m d → value (monomials≤ᶜ n m d) ≡ monomials≤ n m d
value-monomials≤ᶜ n m d =
  trans (value-subᵐ≤ᶜ (⊤ {n}) (⊤ {m}) d) (monomials≡ n m d)


------------------------------------------------------------------------
-- The cost of the enumeration

-- Every listing is non-empty: the empty submonomial is always there.

subsOf≤-nonempty : (p : Subset k) (d : ℕ) → 1 ≤ length (subsOf≤ p d)
subsOf≤-nonempty []            d       = s≤s z≤n
subsOf≤-nonempty (outside ∷ p) d       = ℕ.≤-trans (subsOf≤-nonempty p d)
  (ℕ.≤-reflexive (sym (List.length-map (outside ∷_) (subsOf≤ p d))))
subsOf≤-nonempty (inside  ∷ p) zero    = ℕ.≤-trans (subsOf≤-nonempty p zero)
  (ℕ.≤-reflexive (sym (List.length-map (outside ∷_) (subsOf≤ p zero))))
subsOf≤-nonempty (inside  ∷ p) (suc d) = ℕ.≤-trans
  (subsOf≤-nonempty p (suc d))
  (ℕ.≤-trans (ℕ.m≤n+m _ (length (map (inside ∷_) (subsOf≤ p d))))
    (ℕ.≤-trans
      (ℕ.≤-reflexive (cong (length (map (inside ∷_) (subsOf≤ p d)) +_)
        (sym (List.length-map (outside ∷_) (subsOf≤ p (suc d))))))
      (ℕ.≤-reflexive (sym (List.length-++ (map (inside ∷_) (subsOf≤ p d)))))))

subᵐ≤-nonempty : (α : Subset n) (β : Subset m) (d : ℕ) →
                 1 ≤ length (subᵐ≤ α β d)
subᵐ≤-nonempty []            β d       = ℕ.≤-trans (subsOf≤-nonempty β d)
  (ℕ.≤-reflexive (sym (List.length-map (λ b → [] , b) (subsOf≤ β d))))
subᵐ≤-nonempty (outside ∷ α) β d       = ℕ.≤-trans (subᵐ≤-nonempty α β d)
  (ℕ.≤-reflexive (sym (List.length-map (consˣ outside) (subᵐ≤ α β d))))
subᵐ≤-nonempty (inside  ∷ α) β zero    = ℕ.≤-trans
  (subᵐ≤-nonempty α β zero)
  (ℕ.≤-reflexive (sym (List.length-map (consˣ outside) (subᵐ≤ α β zero))))
subᵐ≤-nonempty (inside  ∷ α) β (suc d) = ℕ.≤-trans
  (subᵐ≤-nonempty α β (suc d))
  (ℕ.≤-trans (ℕ.m≤n+m _ (length (map (consˣ inside) (subᵐ≤ α β d))))
    (ℕ.≤-trans
      (ℕ.≤-reflexive (cong (length (map (consˣ inside) (subᵐ≤ α β d)) +_)
        (sym (List.length-map (consˣ outside) (subᵐ≤ α β (suc d))))))
      (ℕ.≤-reflexive
        (sym (List.length-++ (map (consˣ inside) (subᵐ≤ α β d)))))))

-- The arithmetic of one level of the recursion: a level that maps over
-- the list below it costs at most the length of that list more, and a
-- level that joins two lists at most twice the first and once the
-- second more, which three times the new length pays for.

private
  spread₁ : ∀ c L → 3 * c * L + L + L + L ≡ 3 * suc c * L
  spread₁ = solve 2 (λ c L → con 3 :* c :* L :+ L :+ L :+ L :=
                             con 3 :* (con 1 :+ c) :* L) refl

  spread₂ : ∀ c L₁ L₂ →
            3 * c * L₁ + (3 * c * L₂ + (L₁ + (L₂ + L₁))) + L₂ + (L₁ + L₂) ≡
            3 * suc c * (L₁ + L₂)
  spread₂ = solve 3 (λ c L₁ L₂ →
    con 3 :* c :* L₁ :+ (con 3 :* c :* L₂ :+ (L₁ :+ (L₂ :+ L₁))) :+ L₂
      :+ (L₁ :+ L₂) :=
    con 3 :* (con 1 :+ c) :* (L₁ :+ L₂)) refl

  -- One more step than there is room for, paid by a non-empty list.
  bump : ∀ Y {L} → 1 ≤ L → suc Y ≤ Y + L
  bump Y 1≤L = ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-comm 1 Y)) (ℕ.+-monoʳ-≤ Y 1≤L)

  level₀ : ∀ c {t e L} → t ≤ 3 * c * L → e ≤ L * 1 →
           t + e ≤ 3 * suc c * L
  level₀ c {t} {e} {L} t≤ e≤ = ℕ.≤-trans
    (ℕ.+-mono-≤ t≤ (ℕ.≤-trans e≤ (ℕ.≤-reflexive (ℕ.*-identityʳ L))))
    (ℕ.≤-trans (ℕ.m≤m+n (3 * c * L + L) L)
      (ℕ.≤-trans (ℕ.m≤m+n (3 * c * L + L + L) L)
                 (ℕ.≤-reflexive (spread₁ c L))))

  level₁ : ∀ c {t e L} → t ≤ 3 * c * L → e ≤ L * 1 → 1 ≤ L →
           suc (t + e) ≤ 3 * suc c * L
  level₁ c {t} {e} {L} t≤ e≤ 1≤L = ℕ.≤-trans
    (s≤s (ℕ.+-mono-≤ t≤ (ℕ.≤-trans e≤ (ℕ.≤-reflexive (ℕ.*-identityʳ L)))))
    (ℕ.≤-trans (bump (3 * c * L + L) 1≤L)
      (ℕ.≤-trans (ℕ.m≤m+n (3 * c * L + L + L) L)
                 (ℕ.≤-reflexive (spread₁ c L))))

  level₂ : ∀ c {t₁ t₂ e₁ e₂ e₃ L₁ L₂} →
           t₁ ≤ 3 * c * L₁ → t₂ ≤ 3 * c * L₂ → e₁ ≤ L₁ * 1 →
           e₂ ≤ L₂ * 1 → e₃ ≤ L₁ → 1 ≤ L₂ →
           suc (t₁ + (t₂ + (e₁ + (e₂ + e₃)))) ≤ 3 * suc c * (L₁ + L₂)
  level₂ c {t₁} {t₂} {e₁} {e₂} {e₃} {L₁} {L₂} h₁ h₂ g₁ g₂ g₃ 1≤L₂ =
    ℕ.≤-trans
      (s≤s (ℕ.+-mono-≤ h₁ (ℕ.+-mono-≤ h₂ (ℕ.+-mono-≤
        (ℕ.≤-trans g₁ (ℕ.≤-reflexive (ℕ.*-identityʳ L₁)))
        (ℕ.+-mono-≤ (ℕ.≤-trans g₂ (ℕ.≤-reflexive (ℕ.*-identityʳ L₂)))
                    g₃)))))
      (ℕ.≤-trans (bump Y 1≤L₂)
        (ℕ.≤-trans (ℕ.m≤m+n (Y + L₂) (L₁ + L₂))
                   (ℕ.≤-reflexive (spread₂ c L₁ L₂))))
    where
    Y : ℕ
    Y = 3 * c * L₁ + (3 * c * L₂ + (L₁ + (L₂ + L₁)))

-- The enumeration costs at most 3 (k + 1) times what it produces, and
-- the submonomials 3 (n + m + 2) times.

cost-consAllᶜ : (b : Bool) (ss : List (Subset k)) →
                cost (consAllᶜ b ss) ≤ length ss * 1
cost-consAllᶜ b ss = cost-mapᶜ (λ s → pure (b ∷ s)) ss (λ _ → z≤n)

private
  length-value : (m′ : Cost (List A)) {xs : List A} → value m′ ≡ xs →
                 length (value m′) ≡ length xs
  length-value m′ eq = cong length eq

cost-subsOf≤ᶜ : (p : Subset k) (d : ℕ) →
                cost (subsOf≤ᶜ p d) ≤ 3 * suc k * length (subsOf≤ p d)
cost-subsOf≤ᶜ []            d       = s≤s z≤n
cost-subsOf≤ᶜ {k = suc k} (outside ∷ p) d = ℕ.≤-trans
  (level₁ (suc k) (cost-subsOf≤ᶜ p d)
    (ℕ.≤-trans (cost-consAllᶜ outside (value (subsOf≤ᶜ p d)))
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subsOf≤ᶜ p d)
                                     (value-subsOf≤ᶜ p d)))))
    (subsOf≤-nonempty p d))
  (ℕ.≤-reflexive (cong (3 * suc (suc k) *_)
    (sym (List.length-map (outside ∷_) (subsOf≤ p d)))))
cost-subsOf≤ᶜ {k = suc k} (inside ∷ p) zero = ℕ.≤-trans
  (level₁ (suc k) (cost-subsOf≤ᶜ p zero)
    (ℕ.≤-trans (cost-consAllᶜ outside (value (subsOf≤ᶜ p zero)))
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subsOf≤ᶜ p zero)
                                     (value-subsOf≤ᶜ p zero)))))
    (subsOf≤-nonempty p zero))
  (ℕ.≤-reflexive (cong (3 * suc (suc k) *_)
    (sym (List.length-map (outside ∷_) (subsOf≤ p zero)))))
cost-subsOf≤ᶜ {k = suc k} (inside ∷ p) (suc d) = ℕ.≤-trans
  (level₂ (suc k) (cost-subsOf≤ᶜ p d) (cost-subsOf≤ᶜ p (suc d))
    (ℕ.≤-trans (cost-consAllᶜ inside As)
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subsOf≤ᶜ p d)
                                     (value-subsOf≤ᶜ p d)))))
    (ℕ.≤-trans (cost-consAllᶜ outside Bs)
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subsOf≤ᶜ p (suc d))
                                     (value-subsOf≤ᶜ p (suc d))))))
    (ℕ.≤-trans (cost-appendᶜ (value (consAllᶜ inside As))
                             (value (consAllᶜ outside Bs)))
      (ℕ.≤-reflexive (trans
        (cong length (value-mapᶜ (λ s → pure (inside ∷ s)) As))
        (trans (List.length-map (inside ∷_) As)
               (length-value (subsOf≤ᶜ p d) (value-subsOf≤ᶜ p d))))))
    (subsOf≤-nonempty p (suc d)))
  (ℕ.≤-reflexive (cong (3 * suc (suc k) *_) (sym (trans
    (List.length-++ (map (inside ∷_) (subsOf≤ p d)))
    (cong₂ _+_ (List.length-map (inside ∷_) (subsOf≤ p d))
               (List.length-map (outside ∷_) (subsOf≤ p (suc d))))))))
  where
  As = value (subsOf≤ᶜ p d)
  Bs = value (subsOf≤ᶜ p (suc d))

cost-subᵐ≤ᶜ : (α : Subset n) (β : Subset m) (d : ℕ) →
              cost (subᵐ≤ᶜ α β d) ≤ 3 * suc (n + suc m) * length (subᵐ≤ α β d)
cost-subᵐ≤ᶜ {m = m} []            β d       = ℕ.≤-trans
  (level₀ (suc m) (cost-subsOf≤ᶜ β d)
    (ℕ.≤-trans (cost-mapᶜ (λ b → pure ([] , b)) (value (subsOf≤ᶜ β d))
                          (λ _ → z≤n))
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subsOf≤ᶜ β d)
                                     (value-subsOf≤ᶜ β d))))))
  (ℕ.≤-reflexive (cong (3 * suc (suc m) *_)
    (sym (List.length-map (λ b → [] , b) (subsOf≤ β d)))))
cost-subᵐ≤ᶜ {n = suc n} {m} (outside ∷ α) β d = ℕ.≤-trans
  (level₁ (suc (n + suc m)) (cost-subᵐ≤ᶜ α β d)
    (ℕ.≤-trans (cost-mapᶜ (λ γ → pure (consˣ outside γ))
                          (value (subᵐ≤ᶜ α β d)) (λ _ → z≤n))
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subᵐ≤ᶜ α β d)
                                     (value-subᵐ≤ᶜ α β d)))))
    (subᵐ≤-nonempty α β d))
  (ℕ.≤-reflexive (cong (3 * suc (suc (n + suc m)) *_)
    (sym (List.length-map (consˣ outside) (subᵐ≤ α β d)))))
cost-subᵐ≤ᶜ {n = suc n} {m} (inside ∷ α) β zero = ℕ.≤-trans
  (level₁ (suc (n + suc m)) (cost-subᵐ≤ᶜ α β zero)
    (ℕ.≤-trans (cost-mapᶜ (λ γ → pure (consˣ outside γ))
                          (value (subᵐ≤ᶜ α β zero)) (λ _ → z≤n))
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subᵐ≤ᶜ α β zero)
                                     (value-subᵐ≤ᶜ α β zero)))))
    (subᵐ≤-nonempty α β zero))
  (ℕ.≤-reflexive (cong (3 * suc (suc (n + suc m)) *_)
    (sym (List.length-map (consˣ outside) (subᵐ≤ α β zero)))))
cost-subᵐ≤ᶜ {n = suc n} {m} (inside ∷ α) β (suc d) = ℕ.≤-trans
  (level₂ (suc (n + suc m)) (cost-subᵐ≤ᶜ α β d) (cost-subᵐ≤ᶜ α β (suc d))
    (ℕ.≤-trans (cost-mapᶜ (λ γ → pure (consˣ inside γ)) As (λ _ → z≤n))
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subᵐ≤ᶜ α β d)
                                     (value-subᵐ≤ᶜ α β d)))))
    (ℕ.≤-trans (cost-mapᶜ (λ γ → pure (consˣ outside γ)) Bs (λ _ → z≤n))
      (ℕ.≤-reflexive (cong (_* 1) (length-value (subᵐ≤ᶜ α β (suc d))
                                     (value-subᵐ≤ᶜ α β (suc d))))))
    (ℕ.≤-trans (cost-appendᶜ (value (mapᶜ (λ γ → pure (consˣ inside γ)) As))
                             (value (mapᶜ (λ γ → pure (consˣ outside γ)) Bs)))
      (ℕ.≤-reflexive (trans
        (cong length (value-mapᶜ (λ γ → pure (consˣ inside γ)) As))
        (trans (List.length-map (consˣ inside) As)
               (length-value (subᵐ≤ᶜ α β d) (value-subᵐ≤ᶜ α β d))))))
    (subᵐ≤-nonempty α β (suc d)))
  (ℕ.≤-reflexive (cong (3 * suc (suc (n + suc m)) *_) (sym (trans
    (List.length-++ (map (consˣ inside) (subᵐ≤ α β d)))
    (cong₂ _+_ (List.length-map (consˣ inside) (subᵐ≤ α β d))
               (List.length-map (consˣ outside) (subᵐ≤ α β (suc d))))))))
  where
  As = value (subᵐ≤ᶜ α β d)
  Bs = value (subᵐ≤ᶜ α β (suc d))

cost-monomials≤ᶜ : ∀ n m d →
                   cost (monomials≤ᶜ n m d) ≤
                   3 * suc (n + suc m) * length (monomials≤ n m d)
cost-monomials≤ᶜ n m d = ℕ.≤-trans (cost-subᵐ≤ᶜ (⊤ {n}) (⊤ {m}) d)
  (ℕ.≤-reflexive (cong (λ xs → 3 * suc (n + suc m) * length xs)
                       (monomials≡ n m d)))
