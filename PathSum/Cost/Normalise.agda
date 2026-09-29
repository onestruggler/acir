------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalisation at polynomial cost, and proposition 3.2 (Amy, QPL
-- 2018)
--
-- Proposition 3.2 reads: "Every sequence of rewrites terminates with
-- an irreducible path-sum.  The sequence is linear in the number of
-- path variables m and for an n-qubit path-sum takes time polynomial
-- in n and m."  The sentence before it gives the reason: "each
-- rewrite rule can be matched against in polynomial time, hence every
-- path-sum reduces to a normal form in polynomial time."
-- PathSum.Anywhere proves the first two claims for the rules it
-- formalises: every chain is finite (⟶ᵍ-SN) and has length m − m′
-- (⟶ᵍ*-length).  PathSum.Anywhere.Match proves that a chain can always
-- be continued to an irreducible path-sum, but by an exponential
-- search.  This module adds the time claim, in the cost model of
-- PathSum.Cost.
--
-- The algorithm is written once, in the monad Cost:
--
--    normaliseᶜ d k R = canonicalise R at degree d (PathSum.Cost.Canon),
--                       then normᶜ;
--    normᶜ d k R      = stop if R has no path variable; otherwise try
--                       every variable for a rule
--                       (PathSum.Cost.Search.searchᶜ), continue from
--                       the result if one applies, and stop if none
--                       does.
--
-- The recursion is on the number of path variables, which every rule
-- lowers by one.  So there are at most m rounds, and no fuel is needed.
-- The result is a Normal: the normalisation k′, the number m′ of path
-- variables and the representation R′ that are left.
--
-- The hypotheses: d ≥ 2 (the order of a Clifford phase, and the order
-- of the term [ω] adds), and ξ, with n inputs, normalisation k and m
-- path variables, is represented by R and has a phase of order at most
-- d.  Proved under them:
--
--  * normalise-sound gives a Normalised record.  It holds a dense chain
--    ξ ⟶ᵍ* ξ′ (PathSum.Anywhere) to a path-sum ξ′ that R′ represents;
--    R′ is canonical and of order at most d; and every path-sum R′
--    represents is irreducible (stuck), in particular ξ′ and psʳ k′ R′.
--    The chain ends at a path-sum that R′ represents, not at
--    psʳ k′ R′ itself.  The reducts of the rules are particular
--    polynomials, which agree with ⟦ R′ ⟧ modulo 1, coefficient by
--    coefficient, and not literally.  Up to ≋ they are the same
--    (PathSum.Cost.Normalise.Equivalence).
--  * cost-normᶜ: on a canonical representation the loop costs at most
--    279 (n + m + 3)^(3d+5).  Canonicalising a list of L terms first
--    costs at most (L + 5)(n + m + 2)(n + m + 1)^d (cost-normaliseᶜ),
--    so the whole costs at most (L + 284)(n + m + 3)^(3d+5)
--    (cost-normalise-poly).  With at most (n + m + 1)^d terms, as in
--    any canonical list or any list PathSum.Size builds at degree d, it
--    costs at most 285 (n + m + 3)^(4d+5) (cost-normalise-small), a
--    polynomial in n and m alone.
--  * ⟶ᵍ*-Internal: the steps keep every path variable internal, which
--    lemma 4.3 needs at the end of a Clifford reduction.
--  * Every sequence, not only the algorithm's: any sequence of sparse
--    rewrites from the canonicalised input (PathSum.Cost.Sequence), with
--    any rules at any variables in any order, is a dense chain and
--    costs at most m · 92 (n + m + 3)^(3d+3).
--
-- proposition-3-2 packages these as the paper states them: every chain
-- terminates and has length m − m′, the algorithm's chain ends at an
-- irreducible path-sum, and the algorithm and every sequence of sparse
-- rewrites cost a polynomial.  The bounds are upper bounds and are not
-- tight.  They are polynomial for a fixed order bound d; the exponent
-- grows with d, since a phase of order d can have (n + m + 1)^d terms
-- and the algorithm reads them all.  For Clifford path-sums d = 2.
-- For Clifford+R_k, d = max(2, k) (proposition 2.14, corrected in
-- PathSum.CRK.Circuit).
--
-- What is not covered, and why.  Figure 2 has steps that
-- PathSum.Anywhere does not formalise: [ω] and [HH] with a quotient
-- that is Boolean-valued but not a Z₂-linear form, and [Case]
-- (PathSum.Reduction.General, PathSum.Full).  They are left out of the
-- loop and of the theorem.
--
-- Matching them is not the problem.  Their premises are also read
-- coefficient by coefficient: every coefficient of the quotient must be
-- 0 or ½, and for [HH] y_i must occur only in the monomial y_i; for
-- [Case] the coefficients are multiples of ¼ with given parities.  A
-- canonical list can be checked for these one variable, or one pair
-- of variables, at a time.  That argument is not formalised here.
--
-- The problem is the step after the match.  Every bound here rests on
-- the order invariant Ordᵀ d.  It keeps the phase of degree at most d
-- modulo 1, so with at most (n + m + 1)^d terms, and it is what makes
-- the algorithm's truncations exact: [HH]'s expansion at degree d, and
-- canonicalising at degree d.  Lemma 2.13 keeps the order under
-- substitution of a linear form.  The paper states it for linear Q
-- only, and rightly so, since it fails for non-linear Q:
--
--  * ½y₀y₁ + ½y₀x₀x₁ + ⅛y₁ has order 3, and [HH] with the quotient
--    x₀x₁ leaves ⅛x₀x₁, of order 4 (PathSum.Cost.Excluded proves it at
--    M = 3; PathSum.Polynomial.Substitution has the smaller example
--    ¼y[y ← x₁x₂]);
--  * [Case] multiplies the rest of the phase by X.
--
-- After such a step the order can exceed d.  The truncations are then
-- no longer exact, and the (n + m + 1)^d bound on the number of terms
-- no longer applies.  Nothing in the paper bounds how far the order
-- can rise along a sequence of such steps.  The paper's "hence" --
-- rules matched in polynomial time, hence normalisation in polynomial
-- time -- also needs the path-sum to stay of polynomial size, and
-- lemma 2.13 gives that for linear quotients only.  So no time bound
-- is claimed for these rules.  At order 2 (Clifford path-sums, with
-- internal path variables) every rule of figure 2 keeps the order at 2
-- (PathSum.Full.Clifford), so this obstacle disappears there.  It is
-- not proved here that the loop's irreducible outputs are also
-- irreducible under those rules.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Normalise (M : ℕ) where

open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import PathSum.Anywhere M using
  (_⟶ᵍ_; _⟶ᵍ*_; εᵍ; _◅ᵍ_; plain; at; SN; ⟶ᵍ-SN; lenᵍ; ⟶ᵍ*-length)
open import PathSum.Anywhere.Match M using (Irreducible)
open import PathSum.Base using
  (PathSum; phase; out; Internal; tail-part; tail-Internal)
open import PathSum.Cost
open import PathSum.Cost.Bound using (^-mono)
open import PathSum.Cost.Canon M using
  (canonᶜ; canonᶜ-Canonical; cost-canonᶜ; Canonical; Ordᵀ)
open import PathSum.Cost.Rules M using
  (canon-represents; phase-Ord≤; psʳ-represents)
open import PathSum.Cost.Search M using
  (searchᶜ; search-sound; search-canonical; search-complete; searchBound;
   cost-searchᶜ)
open import PathSum.Cost.Sequence M using
  (Sequence; sequenceBound; sequence-cost)
open import PathSum.Order M using (Ord≤)
open import PathSum.Polynomial using (y[_]; _∖ᵐ_)
open import PathSum.Polynomial.Properties using (subst-NoVar)
open import PathSum.Reduction M using (_⟶_; elim; ω; hh)
open import PathSum.Reorder using (Internal-front)
open import PathSum.Size.Sparse M using
  (Rep; rep; terms; forms; Represents; psʳ)

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    d k n m k′ m′ : ℕ


------------------------------------------------------------------------
-- The algorithm

-- What is left at the end: the normalisation, the number of path
-- variables, and the representation.

record Normal (n : ℕ) : Set where
  constructor normal
  field
    nk   : ℕ
    nm   : ℕ
    nrep : Rep n nm

open Normal public

-- The path-sum it stands for.

psᴺ : (r : Normal n) → PathSum n (nk r) (nm r)
psᴺ r = psʳ (nk r) (nrep r)

-- Search, step, repeat.  The recursion is on the number of path
-- variables, which every step lowers by one.

mutual
  normᶜ : ℕ → ℕ → Rep n m → Cost (Normal n)
  normᶜ {m = zero}  d k R = pure (normal k 0 R)
  normᶜ {m = suc m} d k R = searchᶜ d k R >>= normNext d k R

  normNext : ℕ → ℕ → Rep n (suc m) → Maybe (ℕ × Rep n m) → Cost (Normal n)
  normNext {m = m} d k R nothing           = pure (normal k (suc m) R)
  normNext         d k R (just (k′ , R′)) = normᶜ d k′ R′

-- Canonicalise first.

normaliseᶜ : ℕ → ℕ → Rep n m → Cost (Normal n)
normaliseᶜ d k R = canonᶜ d (terms R) >>= λ ts → normᶜ d k (rep ts (forms R))

-- The canonicalised representation the loop starts from.

canonᴿ : ℕ → Rep n m → Rep n m
canonᴿ d R = rep (value (canonᶜ d (terms R))) (forms R)


------------------------------------------------------------------------
-- What it computes

-- A chain from ξ to a path-sum the result represents, the result
-- canonical and of order at most d, and no rule applicable to any
-- path-sum it represents.

record Normalised (d : ℕ) {n k m : ℕ} (ξ : PathSum n k m)
                  (r : Normal n) : Set where
  field
    reduct            : PathSum n (nk r) (nm r)
    chain             : ξ ⟶ᵍ* reduct
    reduct-represents : Represents reduct (nrep r)
    reduct-ordered    : Ordᵀ d (terms (nrep r))
    reduct-canonical  : Canonical d (terms (nrep r))
    stuck             : (ψ : PathSum n (nk r) (nm r)) →
                        Represents ψ (nrep r) → Irreducible ψ

  -- In particular the end of the chain is irreducible.
  irreducible : Irreducible reduct
  irreducible = stuck reduct reduct-represents

open Normalised public

-- The loop, on a canonical representation of order at most d.

norm-sound : (d : ℕ) → 2 ≤ d → (ξ : PathSum n k m) (R : Rep n m) →
             Represents ξ R → Ordᵀ d (terms R) → Canonical d (terms R) →
             Normalised d ξ (value (normᶜ d k R))
norm-sound {m = zero} d 2≤d ξ R rp ord can = record
  { reduct            = ξ
  ; chain             = εᵍ
  ; reduct-represents = rp
  ; reduct-ordered    = ord
  ; reduct-canonical  = can
  ; stuck             = λ ψ _ → λ { (plain ()) }
  }
norm-sound {n = n} {k = k} {m = suc m} d 2≤d ξ R rp ord can =
  next (value (searchᶜ d k R)) refl
  where
  next : (r : Maybe (ℕ × Rep n m)) → value (searchᶜ d k R) ≡ r →
         Normalised d ξ (value (normNext d k R r))
  next nothing e = record
    { reduct            = ξ
    ; chain             = εᵍ
    ; reduct-represents = rp
    ; reduct-ordered    = ord
    ; reduct-canonical  = can
    ; stuck             = λ ψ rpψ → search-complete d ψ R rpψ can e
    }
  next (just (k′ , R′)) e = record
    { reduct            = reduct N
    ; chain             = proj₁ (proj₂ st) ◅ᵍ chain N
    ; reduct-represents = reduct-represents N
    ; reduct-ordered    = reduct-ordered N
    ; reduct-canonical  = reduct-canonical N
    ; stuck             = stuck N
    }
    where
    st = search-sound d 2≤d ξ R rp ord e
    N  = norm-sound d 2≤d (proj₁ st) R′ (proj₁ (proj₂ (proj₂ st)))
                    (proj₂ (proj₂ (proj₂ st))) (search-canonical d k R e)

-- The whole algorithm, on any representation of a phase of order at
-- most d.

normalise-sound : (d : ℕ) → 2 ≤ d → (ξ : PathSum n k m) (R : Rep n m) →
                  Represents ξ R → Ord≤ d (phase ξ) →
                  Normalised d ξ (value (normaliseᶜ d k R))
normalise-sound d 2≤d ξ R rp ordP =
  norm-sound d 2≤d ξ (rep (value (canonᶜ d (terms R))) (forms R))
    (proj₁ cr , proj₂ rp) (proj₂ cr) (canonᶜ-Canonical d (terms R))
  where
  cr = canon-represents d (terms R) (proj₁ rp) ordP

-- The reduct's phase has order at most d, and the path-sum the result
-- stands for is irreducible too.

reduct-Ord≤ : ∀ {d n k m} {ξ : PathSum n k m} {r : Normal n}
              (N : Normalised d ξ r) → Ord≤ d (phase (reduct N))
reduct-Ord≤ {r = r} N =
  phase-Ord≤ (reduct N) (nrep r) (reduct-represents N) (reduct-ordered N)

psᴺ-irreducible : ∀ {d n k m} {ξ : PathSum n k m} {r : Normal n}
                  (N : Normalised d ξ r) → Irreducible (psᴺ r)
psᴺ-irreducible {r = r} N =
  stuck N (psᴺ r) (psʳ-represents {k = nk r} (nrep r))


------------------------------------------------------------------------
-- The steps keep every path variable internal

⟶-Internal : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
             ξ ⟶ ζ → Internal ξ → Internal ζ
⟶-Internal (elim ξ _ _)       int = tail-Internal ξ int
⟶-Internal (ω ξ _ _ _ _)      int = tail-Internal ξ int
⟶-Internal (hh ξ i c S _ _ _) int j w =
  subst-NoVar (tail-part (out ξ w)) i c (S ∖ᵐ y[ i ])
    (λ j′ → tail-Internal ξ int j′ w) j

⟶ᵍ-Internal : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
              ξ ⟶ᵍ ζ → Internal ξ → Internal ζ
⟶ᵍ-Internal           (plain s) int = ⟶-Internal s int
⟶ᵍ-Internal {ξ = ξ} (at j s)  int = ⟶-Internal s (Internal-front j ξ int)

⟶ᵍ*-Internal : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
               ξ ⟶ᵍ* ζ → Internal ξ → Internal ζ
⟶ᵍ*-Internal εᵍ        int = int
⟶ᵍ*-Internal (s ◅ᵍ ss) int = ⟶ᵍ*-Internal ss (⟶ᵍ-Internal s int)

normalise-Internal : ∀ {d n k m} {ξ : PathSum n k m} {r : Normal n}
                     (N : Normalised d ξ r) → Internal ξ →
                     Internal (reduct N)
normalise-Internal N int = ⟶ᵍ*-Internal (chain N) int


------------------------------------------------------------------------
-- Cost

-- Round by round: at m + 1 path variables a search costs at most
-- (m + 1)(3 + 276 (n + m + 3)^(3d+3)) (PathSum.Cost.Search), and there
-- are at most m rounds.

loopBound : ℕ → ℕ → ℕ → ℕ
loopBound n m d = m * (m * (3 + 276 * (3 + (n + m)) ^ (3 * d + 3)))

private
  Y : ℕ → ℕ → ℕ → ℕ
  Y n m d = 3 + 276 * (3 + (n + m)) ^ (3 * d + 3)

  search≡ : ∀ n m d → searchBound n m d ≡ suc m * Y n m d
  search≡ n m d = cong (λ z → suc m * (3 + z))
    (sym (ℕ.*-assoc 3 92 ((3 + (n + m)) ^ (3 * d + 3))))

  Y-mono : ∀ n m d → Y n m d ≤ Y n (suc m) d
  Y-mono n m d = ℕ.+-monoʳ-≤ 3 (ℕ.*-monoʳ-≤ 276 (ℕ.^-monoˡ-≤ (3 * d + 3)
    (ℕ.+-monoʳ-≤ 3 (ℕ.+-monoʳ-≤ n (ℕ.n≤1+n m)))))

  square : ∀ m Y → suc m * Y + m * (suc m * Y) ≡ suc m * (suc m * Y)
  square = solve 2 (λ m Y → (con 1 :+ m) :* Y :+ m :* ((con 1 :+ m) :* Y) :=
                            (con 1 :+ m) :* ((con 1 :+ m) :* Y)) refl

cost-normᶜ : (d k : ℕ) (R : Rep n m) → Canonical d (terms R) →
             cost (normᶜ d k R) ≤ loopBound n m d
cost-normᶜ {m = zero}          d k R can = z≤n
cost-normᶜ {n = n} {m = suc m} d k R can = ℕ.≤-trans
  (ℕ.+-mono-≤ (ℕ.≤-trans (cost-searchᶜ d k R can)
                         (ℕ.≤-reflexive (search≡ n m d)))
              (next (value (searchᶜ d k R)) refl))
  (ℕ.≤-trans
    (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ (suc m) (Y-mono n m d))
                (ℕ.*-monoʳ-≤ m (ℕ.*-mono-≤ (ℕ.n≤1+n m) (Y-mono n m d))))
    (ℕ.≤-reflexive (square m (Y n (suc m) d))))
  where
  next : (r : Maybe (ℕ × Rep n m)) → value (searchᶜ d k R) ≡ r →
         cost (normNext d k R r) ≤ loopBound n m d
  next nothing          e = z≤n
  next (just (k′ , R′)) e = cost-normᶜ d k′ R′ (search-canonical d k R e)

-- One power: at most 279 (n + m + 3)^(3d+5).

normBound : ℕ → ℕ → ℕ → ℕ
normBound n m d = 279 * (3 + (n + m)) ^ (3 * d + 5)

loop≤norm : ∀ n m d → loopBound n m d ≤ normBound n m d
loop≤norm n m d = ℕ.≤-trans
  (ℕ.*-mono-≤ m≤B (ℕ.*-mono-≤ m≤B Y≤))
  (ℕ.≤-reflexive (trans (shuffle B P) (cong (279 *_) (sym B^))))
  where
  B = 3 + (n + m)
  P = B ^ (3 * d + 3)

  m≤B : m ≤ B
  m≤B = ℕ.≤-trans (ℕ.m≤n+m m n) (ℕ.m≤n+m (n + m) 3)

  1≤P : 1 ≤ P
  1≤P = ℕ.m^n>0 B (3 * d + 3)

  Y≤ : 3 + 276 * P ≤ 279 * P
  Y≤ = ℕ.≤-trans (ℕ.+-monoˡ-≤ (276 * P) (ℕ.*-monoʳ-≤ 3 1≤P))
    (ℕ.≤-reflexive (solve 1 (λ P → con 3 :* P :+ con 276 :* P :=
                                   con 279 :* P) refl P))

  shuffle : ∀ B P → B * (B * (279 * P)) ≡ 279 * (B * (B * P))
  shuffle = solve 2 (λ B P → B :* (B :* (con 279 :* P)) :=
                             con 279 :* (B :* (B :* P))) refl

  B^ : B ^ (3 * d + 5) ≡ B * (B * P)
  B^ = cong (B ^_) (solve 1 (λ d → con 3 :* d :+ con 5 :=
                                   con 2 :+ (con 3 :* d :+ con 3)) refl d)

cost-norm-canonical : (d k : ℕ) (R : Rep n m) → Canonical d (terms R) →
                      cost (normᶜ d k R) ≤ normBound n m d
cost-norm-canonical {n} {m} d k R can =
  ℕ.≤-trans (cost-normᶜ d k R can) (loop≤norm n m d)

-- The whole algorithm: the canonicalisation, then the loop.

cost-normaliseᶜ : (d k : ℕ) (R : Rep n m) →
                  cost (normaliseᶜ d k R) ≤
                  (length (terms R) + 5) * suc (suc (n + m)) *
                  suc (n + m) ^ d + normBound n m d
cost-normaliseᶜ d k R = ℕ.+-mono-≤ (cost-canonᶜ d (terms R))
  (cost-norm-canonical d k (rep (value (canonᶜ d (terms R))) (forms R))
                       (canonᶜ-Canonical d (terms R)))

-- As one polynomial in n + m and the length L of the list: at most
-- (L + 284)(n + m + 3)^(3d+5).

cost-normalise-poly : (d k : ℕ) (R : Rep n m) →
                      cost (normaliseᶜ d k R) ≤
                      (length (terms R) + 284) * (3 + (n + m)) ^ (3 * d + 5)
cost-normalise-poly {n} {m} d k R = ℕ.≤-trans (cost-normaliseᶜ d k R)
  (ℕ.≤-trans (ℕ.+-monoˡ-≤ (normBound n m d) canon≤)
             (ℕ.≤-reflexive (join (length (terms R)) (B ^ (3 * d + 5)))))
  where
  B = 3 + (n + m)
  L = length (terms R)

  1≤B : 1 ≤ B
  1≤B = s≤s z≤n

  d<e : suc d ≤ 3 * d + 5
  d<e = ℕ.≤-trans (ℕ.m≤m+n (suc d) (2 * d + 4))
    (ℕ.≤-reflexive (solve 1 (λ d → (con 1 :+ d) :+ (con 2 :* d :+ con 4) :=
                                   con 3 :* d :+ con 5) refl d))

  canon≤ : (L + 5) * suc (suc (n + m)) * suc (n + m) ^ d ≤
           (L + 5) * B ^ (3 * d + 5)
  canon≤ = ℕ.≤-trans
    (ℕ.*-mono-≤ (ℕ.*-monoʳ-≤ (L + 5) (ℕ.n≤1+n (suc (suc (n + m)))))
                (ℕ.^-monoˡ-≤ d (ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.n≤1+n _))))
    (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.*-assoc (L + 5) B (B ^ d)))
               (ℕ.*-monoʳ-≤ (L + 5) (^-mono {k = suc d} 1≤B d<e)))

  join : ∀ L P → (L + 5) * P + 279 * P ≡ (L + 284) * P
  join = solve 2 (λ L P → (L :+ con 5) :* P :+ con 279 :* P :=
                          (L :+ con 284) :* P) refl

-- With at most (n + m + 1)^d terms -- a canonical list, or one that
-- PathSum.Size builds at degree d -- a polynomial in n and m alone.

cost-normalise-small : (d k : ℕ) (R : Rep n m) →
                       length (terms R) ≤ suc (n + m) ^ d →
                       cost (normaliseᶜ d k R) ≤
                       285 * (3 + (n + m)) ^ (4 * d + 5)
cost-normalise-small {n} {m} d k R L≤ = ℕ.≤-trans (cost-normalise-poly d k R)
  (ℕ.≤-trans (ℕ.*-monoˡ-≤ (B ^ (3 * d + 5)) L284≤)
    (ℕ.≤-reflexive (trans (ℕ.*-assoc 285 (B ^ d) (B ^ (3 * d + 5)))
      (cong (285 *_) (trans (sym (ℕ.^-distribˡ-+-* B d (3 * d + 5)))
        (cong (B ^_) (solve 1 (λ d → d :+ (con 3 :* d :+ con 5) :=
                                     con 4 :* d :+ con 5) refl d)))))))
  where
  B = 3 + (n + m)

  1≤B^d : 1 ≤ B ^ d
  1≤B^d = ℕ.m^n>0 B d

  L284≤ : length (terms R) + 284 ≤ 285 * B ^ d
  L284≤ = ℕ.≤-trans
    (ℕ.+-mono-≤ (ℕ.≤-trans L≤ (ℕ.^-monoˡ-≤ d (ℕ.≤-trans (ℕ.n≤1+n _)
                                                        (ℕ.n≤1+n _))))
                (ℕ.*-monoʳ-≤ 284 1≤B^d))
    (ℕ.≤-reflexive (solve 1 (λ X → X :+ con 284 :* X := con 285 :* X) refl
                            (B ^ d)))


------------------------------------------------------------------------
-- Proposition 3.2

-- "Every sequence of rewrites terminates with an irreducible path-sum.
-- The sequence is linear in the number of path variables m and for an
-- n-qubit path-sum takes time polynomial in n and m."  For the rules of
-- PathSum.Anywhere, at order bound d ≥ 2, in the cost model of
-- PathSum.Cost:
--
--  * every chain is finite and has length m − m′;
--  * the algorithm's chain ends at an irreducible path-sum, and the
--    algorithm costs at most (L + 284)(n + m + 3)^(3d+5) for an input
--    of L terms;
--  * every sequence of sparse rewrites (PathSum.Cost.Sequence) from the
--    canonicalised input costs at most m · 92 (n + m + 3)^(3d+3).

record Proposition-3-2 (d : ℕ) {n k m : ℕ} (ξ : PathSum n k m)
                       (R : Rep n m) : Set where
  field
    terminates : SN _⟶ᵍ_ ξ
    linear     : ∀ {k′ m′} {ζ : PathSum n k′ m′} (steps : ξ ⟶ᵍ* ζ) →
                 lenᵍ steps + m′ ≡ m
    normalises : Normalised d ξ (value (normaliseᶜ d k R))
    polynomial : cost (normaliseᶜ d k R) ≤
                 (length (terms R) + 284) * (3 + (n + m)) ^ (3 * d + 5)
    every      : ∀ {k′ m′ c} {R′ : Rep n m′} →
                 Sequence d k (canonᴿ d R) k′ R′ c → c ≤ sequenceBound n m d

proposition-3-2 : (d : ℕ) → 2 ≤ d → (ξ : PathSum n k m) (R : Rep n m) →
                  Represents ξ R → Ord≤ d (phase ξ) → Proposition-3-2 d ξ R
proposition-3-2 {k = k} d 2≤d ξ R rp ordP = record
  { terminates = ⟶ᵍ-SN ξ
  ; linear     = ⟶ᵍ*-length
  ; normalises = normalise-sound d 2≤d ξ R rp ordP
  ; polynomial = cost-normalise-poly d k R
  ; every      = sequence-cost (canonᶜ-Canonical d (terms R))
  }
