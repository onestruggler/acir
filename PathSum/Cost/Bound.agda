------------------------------------------------------------------------
-- Presentations of groups
--
-- Adding up polynomial cost bounds (for Amy, QPL 2018,
-- proposition 3.2)
--
-- The cost of every rule on the sparse representation is bounded by a
-- constant times  (L + 1) · B^e,  where L is the length of the list of
-- terms, B bounds the number of variables (plus a small constant) and
-- e depends on the degree d only.  A program's cost is a sum over its
-- parts, and each part has its own natural bound -- n (m + 3), L B, a
-- canonicalisation's (L + 5)(N + 2)(N + 1)^d, ... -- so the bounds are
-- brought to the common shape one part at a time (lift-B, lift-LB) and
-- then added (≤-+ᶜ), the constants adding up.  Nothing here is about
-- programs: it is arithmetic on ℕ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Cost.Bound where

open import Data.Nat.Base using
  (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; >-nonZero)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    a b c c′ k e L B X : ℕ


------------------------------------------------------------------------
-- The common shape

-- (L + 1) · B^e.

Bnd : ℕ → ℕ → ℕ → ℕ
Bnd L B e = suc L * B ^ e

-- Powers of a positive base are positive and grow with the exponent.

^-pos : 1 ≤ B → 1 ≤ B ^ k
^-pos {B = zero}  ()
^-pos {B = suc B} {k} _ = ℕ.m^n>0 (suc B) k

^-mono : 1 ≤ B → k ≤ e → B ^ k ≤ B ^ e
^-mono {B = zero}  ()
^-mono {B = suc B} _ k≤e = ℕ.^-monoʳ-≤ (suc B) k≤e

-- B · B^k is B^(k+1), and B · B is B².

^-suc : ∀ B k → B * B ^ k ≡ B ^ suc k
^-suc B k = refl

B*B : ∀ B → B * B ≡ B ^ 2
B*B B = cong (B *_) (sym (ℕ.*-identityʳ B))

-- A bound by a power, or by L times a power, is a bound by the common
-- shape at any larger exponent.

lift-B : ∀ L B k e → 1 ≤ B → k ≤ e → a ≤ B ^ k → a ≤ Bnd L B e
lift-B L B k e 1≤B k≤e a≤ = ℕ.≤-trans a≤
  (ℕ.≤-trans (^-mono 1≤B k≤e) (ℕ.m≤m+n (B ^ e) (L * B ^ e)))

lift-LB : ∀ L B k e → 1 ≤ B → k ≤ e → a ≤ L * B ^ k → a ≤ Bnd L B e
lift-LB L B k e 1≤B k≤e a≤ = ℕ.≤-trans a≤
  (ℕ.≤-trans (ℕ.*-monoʳ-≤ L (^-mono 1≤B k≤e)) (ℕ.m≤n+m (L * B ^ e) (B ^ e)))

-- A bound by c copies of X.  It is a record, not a definition, so that
-- c and X are read off it rather than solved for (c * X reduces).

infix 4 _≤[_]_

record _≤[_]_ (a c X : ℕ) : Set where
  constructor bound
  field
    unbound : a ≤ c * X

open _≤[_]_ public

-- Bounds with constants add up.

≤-1ᶜ : a ≤ X → a ≤[ 1 ] X
≤-1ᶜ {X = X} a≤ = bound (ℕ.≤-trans a≤ (ℕ.≤-reflexive (sym (ℕ.+-identityʳ X))))

≤-*ᶜ : ∀ c → a ≤ X → c * a ≤[ c ] X
≤-*ᶜ c a≤ = bound (ℕ.*-monoʳ-≤ c a≤)

≤-scaleᶜ : ∀ c → a ≤ X → a ≤ c * a → a ≤[ c ] X
≤-scaleᶜ c a≤ ca = bound (ℕ.≤-trans ca (ℕ.*-monoʳ-≤ c a≤))

≤-+ᶜ : a ≤[ c ] X → b ≤[ c′ ] X → a + b ≤[ c + c′ ] X
≤-+ᶜ {c = c} {X = X} {c′ = c′} (bound a≤) (bound b≤) =
  bound (ℕ.≤-trans (ℕ.+-mono-≤ a≤ b≤)
                   (ℕ.≤-reflexive (sym (ℕ.*-distribʳ-+ X c c′))))

≤-0ᶜ : 0 ≤[ 0 ] X
≤-0ᶜ = bound z≤n

≤-weakenᶜ : a ≤ b → b ≤[ c ] X → a ≤[ c ] X
≤-weakenᶜ a≤b (bound b≤) = bound (ℕ.≤-trans a≤b b≤)

-- A constant multiple of the shape at a smaller exponent is one at a
-- larger exponent.

Bnd-mono : 1 ≤ B → k ≤ e → c * Bnd L B k ≤ c * Bnd L B e
Bnd-mono {B = B} {k} {e} {c = c} {L = L} 1≤B k≤e =
  ℕ.*-monoʳ-≤ c (ℕ.*-monoʳ-≤ (suc L) (^-mono 1≤B k≤e))

-- The shape grows with L and with the exponent.

Bnd-≤ : ∀ {L L′} → 1 ≤ B → L ≤ L′ → k ≤ e → Bnd L B k ≤ Bnd L′ B e
Bnd-≤ 1≤B L≤L′ k≤e = ℕ.*-mono-≤ (s≤s L≤L′) (^-mono 1≤B k≤e)

≤ᶜ-mono : ∀ {x L L′} → 1 ≤ B → L ≤ L′ → k ≤ e →
          x ≤[ c ] Bnd L B k → x ≤[ c ] Bnd L′ B e
≤ᶜ-mono {c = c} 1≤B L≤L′ k≤e (bound x≤) =
  bound (ℕ.≤-trans x≤ (ℕ.*-monoʳ-≤ c (Bnd-≤ 1≤B L≤L′ k≤e)))

-- When L ≤ B^d, as for a canonical list (at most one term per
-- monomial of degree at most d), (L + 1) B^e ≤ 2 B^(d+e).

Bnd-small : ∀ {L d} → 1 ≤ B → L ≤ B ^ d → Bnd L B e ≤ 2 * B ^ (d + e)
Bnd-small {B = B} {e = e} {L = L} {d = d} 1≤B L≤ = ℕ.≤-trans
  (ℕ.*-monoˡ-≤ (B ^ e) (ℕ.≤-trans (s≤s L≤)
    (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-comm 1 (B ^ d)))
               (ℕ.+-monoʳ-≤ (B ^ d) (^-pos {k = d} 1≤B)))))
  (ℕ.≤-reflexive (trans (twice (B ^ d) (B ^ e))
                        (cong (2 *_) (sym (ℕ.^-distribˡ-+-* B d e)))))
  where
  twice : ∀ x y → (x + x) * y ≡ 2 * (x * y)
  twice = solve 2 (λ x y → (x :+ x) :* y := con 2 :* (x :* y)) refl
