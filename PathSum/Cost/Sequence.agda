------------------------------------------------------------------------
-- Presentations of groups
--
-- Every sequence of sparse rewrites costs a polynomial (for Amy, QPL
-- 2018, proposition 3.2)
--
-- Proposition 3.2 says that every sequence of rewrites "takes time
-- polynomial in n and m", not only the one some algorithm picks.  On
-- the sparse representation a sequence of rewrites is a Sequence: a
-- list of successful applications of the sparse rules of
-- PathSum.Cost.Rules -- [Elim], [ω] or [HH] -- each at any path
-- variable y_j, in any order.  [Elim] and [ω] consume the normalisation
-- they need, so the type tracks it.  The sequence is indexed by its
-- total cost, the sum of the costs of the rule applications, each
-- including its match.
--
-- Proved:
--
--  * sequence-sound: a Sequence from R is a dense chain.  For any ξ
--    that R represents whose terms have order at most d (d ≥ 2),
--    ξ ⟶ᵍ* ξ′ for a ξ′ that the last representation represents, whose
--    terms again have order at most d;
--  * sequence-canonical: from a canonical representation every
--    representation reached is canonical;
--  * sequence-length: a sequence from m to m′ path variables has
--    exactly m − m′ rewrites;
--  * sequence-cost: from a canonical representation with n inputs and
--    m path variables, every sequence costs at most
--    m · 92 (n + m + 3)^(3d+3).  Each rewrite, on the canonical
--    representation it starts from, costs at most 92 (n + m + 3)^(3d+3)
--    (PathSum.Cost.Rules.canonical-cost), and there are at most m.
--
-- [HH]'s substituted variable is the one its matcher picks (the first
-- path variable of the support), so a Sequence is a sequence of the
-- sparse calculus.  A dense chain that substitutes another variable is
-- not literally one of them.  The cost of deciding that nothing
-- applies at the end is the search of PathSum.Cost.Search.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Sequence (M : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (zero; suc; _+_; _*_; _^_; _≤_; z≤n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong)

open import PathSum.Anywhere M using (_⟶ᵍ*_; εᵍ; _◅ᵍ_)
open import PathSum.Base using (PathSum)
open import PathSum.Cost using (value; cost)
open import PathSum.Cost.Canon M using (Canonical; Ordᵀ)
open import PathSum.Cost.Rules M using
  (elimˢ; ωˢ; hhˢ; elimˢ-sound; ωˢ-sound; hhˢ-sound; elimˢ-canonical;
   ωˢ-canonical; hhˢ-canonical; canonical-cost)
open import PathSum.Polynomial using (Mon)
open import PathSum.Reorder using (front)
open import PathSum.Reduction M using (elim-reduct; ω-reduct; hh-reduct)
open import PathSum.Size.Sparse M using (Rep; terms; Represents)

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    d n : ℕ


------------------------------------------------------------------------
-- Sequences of sparse rewrites

-- Sequence d k R k′ R′ c: from the representation R at normalisation k
-- to R′ at normalisation k′, at total cost c.

data Sequence (d : ℕ) {n : ℕ} :
     ∀ {m m′} → ℕ → Rep n m → ℕ → Rep n m′ → ℕ → Set where
  stop  : ∀ {m k} {R : Rep n m} → Sequence d k R k R 0
  elimᵗ : ∀ {m m′ k k′ c} {R : Rep n (suc m)} {R₁ : Rep n m}
          {R′ : Rep n m′} (j : Fin (suc m)) →
          value (elimˢ d j R) ≡ just R₁ →
          Sequence d k R₁ k′ R′ c →
          Sequence d (suc (suc k)) R k′ R′ (cost (elimˢ d j R) + c)
  ωᵗ    : ∀ {m m′ k k′ c} {b : Bool} {S : Mon n m} {R : Rep n (suc m)}
          {R₁ : Rep n m} {R′ : Rep n m′} (j : Fin (suc m)) →
          value (ωˢ d j R) ≡ just (b , S , R₁) →
          Sequence d k R₁ k′ R′ c →
          Sequence d (suc k) R k′ R′ (cost (ωˢ d j R) + c)
  hhᵗ   : ∀ {m m′ k k′ c} {i : Fin m} {b : Bool} {S : Mon n m}
          {R : Rep n (suc m)} {R₁ : Rep n m} {R′ : Rep n m′}
          (j : Fin (suc m)) →
          value (hhˢ d j R) ≡ just (i , b , S , R₁) →
          Sequence d k R₁ k′ R′ c →
          Sequence d k R k′ R′ (cost (hhˢ d j R) + c)

-- The number of rewrites.

rewrites : ∀ {m m′ k k′ c} {R : Rep n m} {R′ : Rep n m′} →
           Sequence d k R k′ R′ c → ℕ
rewrites stop            = 0
rewrites (elimᵗ _ _ seq) = suc (rewrites seq)
rewrites (ωᵗ _ _ seq)    = suc (rewrites seq)
rewrites (hhᵗ _ _ seq)   = suc (rewrites seq)


------------------------------------------------------------------------
-- What a sequence stands for

-- A dense chain, from any path-sum the first representation
-- represents.

sequence-sound : 2 ≤ d → ∀ {m m′ k k′ c} {R : Rep n m} {R′ : Rep n m′} →
                 Sequence d k R k′ R′ c →
                 (ξ : PathSum n k m) → Represents ξ R → Ordᵀ d (terms R) →
                 Σ (PathSum n k′ m′) λ ξ′ →
                   (ξ ⟶ᵍ* ξ′) × Represents ξ′ R′ × Ordᵀ d (terms R′)
sequence-sound 2≤d stop ξ rp ord = ξ , εᵍ , rp , ord
sequence-sound {d = d} 2≤d {R = R} (elimᵗ j e seq) ξ rp ord =
  proj₁ rest , proj₁ st ◅ᵍ proj₁ (proj₂ rest) , proj₂ (proj₂ rest)
  where
  st   = elimˢ-sound d j ξ R rp ord e
  rest = sequence-sound 2≤d seq (elim-reduct (front j ξ))
                        (proj₁ (proj₂ st)) (proj₂ (proj₂ st))
sequence-sound {d = d} 2≤d {R = R} (ωᵗ {b = b} {S = S} j e seq) ξ rp ord =
  proj₁ rest , proj₁ st ◅ᵍ proj₁ (proj₂ rest) , proj₂ (proj₂ rest)
  where
  st   = ωˢ-sound d 2≤d j ξ R rp ord e
  rest = sequence-sound 2≤d seq (ω-reduct (front j ξ) b S)
                        (proj₁ (proj₂ st)) (proj₂ (proj₂ st))
sequence-sound {d = d} 2≤d {R = R}
               (hhᵗ {i = i} {b = b} {S = S} j e seq) ξ rp ord =
  proj₁ rest , proj₁ st ◅ᵍ proj₁ (proj₂ rest) , proj₂ (proj₂ rest)
  where
  st   = hhˢ-sound d j ξ R rp ord e
  rest = sequence-sound 2≤d seq (hh-reduct (front j ξ) i b S)
                        (proj₁ (proj₂ st)) (proj₂ (proj₂ st))

-- From a canonical representation every representation reached is
-- canonical.

sequence-canonical : ∀ {m m′ k k′ c} {R : Rep n m} {R′ : Rep n m′} →
                     Canonical d (terms R) → Sequence d k R k′ R′ c →
                     Canonical d (terms R′)
sequence-canonical can stop = can
sequence-canonical {d = d} {R = R} can (elimᵗ j e seq) =
  sequence-canonical (elimˢ-canonical d j R e) seq
sequence-canonical {d = d} {R = R} can (ωᵗ j e seq) =
  sequence-canonical (ωˢ-canonical d j R e) seq
sequence-canonical {d = d} {R = R} can (hhᵗ j e seq) =
  sequence-canonical (hhˢ-canonical d j R e) seq

-- Every rewrite removes one path variable.

sequence-length : ∀ {m m′ k k′ c} {R : Rep n m} {R′ : Rep n m′} →
                  (seq : Sequence d k R k′ R′ c) → rewrites seq + m′ ≡ m
sequence-length stop            = refl
sequence-length (elimᵗ _ _ seq) = cong suc (sequence-length seq)
sequence-length (ωᵗ _ _ seq)    = cong suc (sequence-length seq)
sequence-length (hhᵗ _ _ seq)   = cong suc (sequence-length seq)


------------------------------------------------------------------------
-- The cost of a sequence

-- At most m · 92 (n + m + 3)^(3d+3) from a canonical representation
-- with m path variables.

sequenceBound : ℕ → ℕ → ℕ → ℕ
sequenceBound n m d = m * (92 * (3 + (n + m)) ^ (3 * d + 3))

private
  X-mono : ∀ n m d → 92 * (3 + (n + m)) ^ (3 * d + 3) ≤
                     92 * (3 + (n + suc m)) ^ (3 * d + 3)
  X-mono n m d = ℕ.*-monoʳ-≤ 92 (ℕ.^-monoˡ-≤ (3 * d + 3)
    (ℕ.+-monoʳ-≤ 3 (ℕ.+-monoʳ-≤ n (ℕ.n≤1+n m))))

  -- One rewrite at m + 1 path variables, and the rest.
  one-more : ∀ n m d {a b} → a ≤ 92 * (3 + (n + m)) ^ (3 * d + 3) →
             b ≤ sequenceBound n m d → a + b ≤ sequenceBound n (suc m) d
  one-more n m d {a} {b} a≤ b≤ = ℕ.≤-trans (ℕ.+-mono-≤ a≤ b≤)
    (ℕ.≤-trans (ℕ.+-mono-≤ (X-mono n m d) (ℕ.*-monoʳ-≤ m (X-mono n m d)))
               ℕ.≤-refl)

sequence-cost : ∀ {m m′ k k′ c} {R : Rep n m} {R′ : Rep n m′} →
                Canonical d (terms R) → Sequence d k R k′ R′ c →
                c ≤ sequenceBound n m d
sequence-cost can stop = z≤n
sequence-cost {n = n} {d = d} {m = suc m} {R = R} can (elimᵗ j e seq) =
  one-more n m d (proj₁ (canonical-cost d j R can))
    (sequence-cost (elimˢ-canonical d j R e) seq)
sequence-cost {n = n} {d = d} {m = suc m} {R = R} can (ωᵗ j e seq) =
  one-more n m d (proj₁ (proj₂ (canonical-cost d j R can)))
    (sequence-cost (ωˢ-canonical d j R e) seq)
sequence-cost {n = n} {d = d} {m = suc m} {R = R} can (hhᵗ j e seq) =
  one-more n m d (proj₂ (proj₂ (canonical-cost d j R can)))
    (sequence-cost (hhˢ-canonical d j R e) seq)
