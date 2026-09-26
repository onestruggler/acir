------------------------------------------------------------------------
-- Presentations of groups
--
-- A sparse interpreter for circuits, and the size of its data (Amy,
-- QPL 2018, corollary 2.15, its second half)
--
-- Corollary 2.15 ends: "... and can be computed in polynomial time."
-- Running time is a property of a machine, and no machine model -- no
-- Turing machine, no RAM, no cost semantics for Agda's own evaluation
-- -- is formalised here; so that sentence is not formalised, and no
-- complexity class is.  What is formalised is as much of it as can be
-- stated without one: an explicit program that computes a
-- representation of the path-sum of a circuit over {H, CNOT, R_k,
-- R_k†} gate by gate, on sparse data, proved correct; and bounds on
-- the size of the data it computes -- the terms each gate produces,
-- the terms of the result and of every intermediate state, and of all
-- of them together -- polynomial in n + |C| for fixed k.  These bound
-- the size of the computation's data, not the running time of a
-- Turing machine.  That each step does work polynomial in the data it
-- reads and writes (a map over the list, an enumeration of the subsets
-- of one form's variables, one pass over the list per coefficient when
-- compacting) is evident from the definitions, but it is not a theorem
-- here.
--
-- The plan.
--
--  1. State.  The interpreter's state is a PathSum.Size.Sparse.Rep n m:
--     a list of terms (monomial, numerator mod 2^M) for the phase, and
--     a Z₂-linear form (PathSum.Linear.Lin, n + m + 1 bits) on each
--     wire.  It starts with no terms and the inputs on the wires
--     (initˢ).
--  2. Gates (runˢ), the sparse images of PathSum.CRK.Circuit's steps;
--     the forms change exactly as there.
--       R_k on w   prepends liftTerms (2^(M-k)) k (form on w): the
--                  lifting of the form c ⊕ ⨁S scaled by 2^(M-k) and
--                  written out on the submonomials S′ ⊆ S of degree
--                  at most k, with coefficients 2^(M-k) (1-2c)
--                  (-2)^(|S′|-1), and 2^(M-k) c at S′ = ∅
--                  (PathSum.Size.Terms); the terms of higher degree
--                  vanish modulo 1, by lemma 2.13's expansion;
--       R_k† on w  the same with -2^(M-k);
--       H on w     reads every term with a fresh path variable y₀
--                  (wkᵀ), prepends ½ y₀ times the lifting of the form
--                  truncated at degree 1 -- the constant and one term
--                  per variable of the form, the rest vanishing modulo
--                  1 once halved -- and puts y₀ on the wire;
--       CNOT c t   adds the form on c to the form on t.
--     Nothing is merged or dropped.
--  3. Correctness (interpᴷ-correct).  Run alongside
--     PathSum.CRK.Circuit.run, the sparse state tracks the dense one:
--     its terms sum to the dense phase modulo 2^M, coefficient by
--     coefficient, and its forms are the dense state's (Agree,
--     runˢ-agree, gate by gate from PathSum.Size.Terms).  So the
--     result denotes ⟦ C ⟧ (Denotes): it has exactly paths C path
--     variables -- which the interpreter computes, it is not told --
--     and represents ⟦ C ⟧ in the sense of Sparse.Represents
--     (denotes-represents).  PathSum.Size.Interpreter.Equivalence
--     turns that into ⟦ C ⟧ ≋ psʳ (norm C) (proj₂ (interpᴷ C)).
--  4. Per gate.  R_k on a form of weight s (the number of variables
--     it adds up) prepends exactly Σ_{i ≤ k} C(s, i) terms, R_k†
--     likewise (stepRˢ-length, stepR†ˢ-length); H exactly s + 1
--     (stepHˢ-length); CNOT none.  As s ≤ n + m: at most
--     (n + m + 1)^k, n + m + 1 and 0 (gate-length).
--  5. In total.  m ≤ |C| throughout, so the result has at most
--     |C| (n + |C| + 1)^max(1,k) terms (interpᴷ-length), k being the
--     level of C (the largest k of an R_k or R_k† in it), hence at
--     most (n + |C| + 1)^(max(1,k)+1) (interpᴷ-length-poly); so does
--     every intermediate state, the result on a prefix (runˢ-++,
--     interpᴷ-prefix), and all the states of the run together have at
--     most |C| + 1 times as many (traceˢ, interpᴷ-trace), at most
--     (n + |C| + 1)^(max(1,k)+2) (interpᴷ-trace-poly).  In bits
--     (Sparse.size) the result, and every intermediate state, has at
--     most 2 (n + |C| + M + 1)^(max(1,k)+2) (interpᴷ-size,
--     interpᴷ-prefix-size).
--  6. Compaction.  Every term has degree at most max(2, k)
--     (interpᴷ-small), so merging the list into one coefficient per
--     monomial of degree at most max(2, k) loses nothing (compact:
--     Sparse.sparse of the list's own sum, each coefficient of which
--     is read off the list).  The result, compactᴷ C, still denotes
--     ⟦ C ⟧, with at most (n + |C| + 1)^max(2,k) terms and
--     2 (n + |C| + M + 1)^(max(2,k)+1) bits; indeed it is exactly the
--     representation PathSum.Size reads off the dense phase
--     (compactᴷ≡repᴷ, residues depending on the phase only modulo
--     2^M), here reached gate by gate.  corollary-2-15ᴷ-sparse
--     collects 3-6.
--
-- PathSum.Size.Interpreter.Clifford does the same over {H, S, CZ},
-- where every gate prepends exactly one term, and
-- PathSum.Size.Interpreter.Example runs the interpreter on the seven-T
-- Toffoli circuit: 30 terms, 21 of them nonzero, compacted to the 26
-- of PathSum.Size.Example, three of them nonzero.
--
-- Remarks.  The degree bound max(2, k), not k, is proposition 2.14's
-- corrected bound (PathSum.CRK.Circuit.prop-2-14-false-at-1).  M is
-- the precision of the phase, a module parameter, and R_k is
-- interpreted exactly only for k ≤ M (PathSum.CRK.Circuit).  The
-- uncompacted list can be longer than the compacted one --
-- |C| (n + |C| + 1)^max(1,k) terms against (n + |C| + 1)^max(2,k) --
-- because repeated monomials are not merged as they arise; the paper
-- does not say how the phase is stored while it is built, and either
-- way the size is polynomial in n + |C| for fixed k.  The exponent
-- max(1,k) of the list, below the max(2,k) of the degree bound, is
-- not a slip: a Hadamard adds degree-2 terms, but only n + m + 1 of
-- them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Size.Interpreter (M : ℕ) where

open import Data.Fin.Base using (Fin; zero)
open import Data.Fin.Subset using (∣_∣)
open import Data.Integer.Base using (-_)
  renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _∸_; _^_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ; wkLin; _⊕ᴸ_; mul-y₀)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (x[_]; y[_]; ∥_∥; _≈[_]_; _+ᴾ_; _-ᴾ_; _·ᴾ_)
open import PathSum.Polynomial.Product using (≈-refl; ≈-sym; ≈-trans)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Reduction M using (½)
open import PathSum.Size M using (norm≤lengthᴷ; paths≤lengthᴷ; repᴷ)
open import PathSum.Size.Monomials using (binomials)
open import PathSum.Size.Sparse M using
  (Term; ⟦_⟧ˢ; Rep; rep; terms; forms; Represents; Small; size;
   sparse; sparse-≈; sparse-small; sparse-length; small-Deg≤;
   size-bound)
open import PathSum.Size.Terms M using
  (≈-++; ≈-≗; wkᵀ; y₀ᵀ; wk-≈; y₀-≈; liftTerms; liftTerms-≈; Deg≤-R;
   Deg≤-R†; Deg≤-H; weight; weight≤; liftTerms-length;
   liftTerms-length≤; binomials-1; liftTerms-small; sparse-cong)

import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Properties as ℕ
import PathSum.CRK.Circuit

private
  module K = PathSum.CRK.Circuit M

open K using (_[_↦_])

private
  variable
    n m k : ℕ


------------------------------------------------------------------------
-- The interpreter

-- No terms, and the inputs on the wires.

initˢ : Rep n 0
initˢ = rep [] (λ w → varᴸ x[ w ])

-- The gates.

stepRˢ : ℕ → Fin n → Rep n m → Rep n m
stepRˢ k w R =
  rep (liftTerms (pow (M ∸ k)) k (forms R w) ++ terms R) (forms R)

stepR†ˢ : ℕ → Fin n → Rep n m → Rep n m
stepR†ˢ k w R =
  rep (liftTerms (- pow (M ∸ k)) k (forms R w) ++ terms R) (forms R)

stepCNOTˢ : Fin n → Fin n → Rep n m → Rep n m
stepCNOTˢ c t R = rep (terms R) (forms R [ t ↦ (forms R t ⊕ᴸ forms R c) ])

stepHˢ : Fin n → Rep n m → Rep n (suc m)
stepHˢ w R =
  rep (map y₀ᵀ (liftTerms ½ 1 (forms R w)) ++ map wkᵀ (terms R))
      ((λ v → wkLin (forms R v)) [ w ↦ varᴸ y[ zero ] ])

-- The circuit, left to right.

runˢ : K.Circuit n → Rep n m → ∃ (Rep n)
runˢ []                 R = _ , R
runˢ (K.H w ∷ C)        R = runˢ C (stepHˢ w R)
runˢ (K.CNOT c t _ ∷ C) R = runˢ C (stepCNOTˢ c t R)
runˢ (K.R k w ∷ C)      R = runˢ C (stepRˢ k w R)
runˢ (K.R† k w ∷ C)     R = runˢ C (stepR†ˢ k w R)

interpᴷ : K.Circuit n → ∃ (Rep n)
interpᴷ C = runˢ C initˢ

-- Running a concatenation runs the second circuit from the state the
-- first leaves: the states of a run are the results on its prefixes.

runˢ-++ : (C D : K.Circuit n) (R : Rep n m) →
          runˢ (C ++ D) R ≡ runˢ D (proj₂ (runˢ C R))
runˢ-++ []                 D R = refl
runˢ-++ (K.H w ∷ C)        D R = runˢ-++ C D (stepHˢ w R)
runˢ-++ (K.CNOT c t _ ∷ C) D R = runˢ-++ C D (stepCNOTˢ c t R)
runˢ-++ (K.R k w ∷ C)      D R = runˢ-++ C D (stepRˢ k w R)
runˢ-++ (K.R† k w ∷ C)     D R = runˢ-++ C D (stepR†ˢ k w R)


------------------------------------------------------------------------
-- Correctness

-- A sparse state agrees with a dense one when they have the same
-- number of path variables and the same forms, and the terms sum to
-- the dense phase modulo 2^M.

data Agree {n : ℕ} : ∃ (Rep n) → ∃ (K.State n) → Set where
  agree : ∀ {m} (ts : List (Term n m)) (st : K.State n m) →
          K.poly st ≈[ pow M ] ⟦ ts ⟧ˢ →
          Agree (m , rep ts (K.sig st)) (m , st)

-- Every gate preserves agreement.

runˢ-agree : (C : K.Circuit n) (ts : List (Term n m)) (st : K.State n m) →
             K.poly st ≈[ pow M ] ⟦ ts ⟧ˢ →
             Agree (runˢ C (rep ts (K.sig st))) (K.run C st)
runˢ-agree []                 ts st h = agree ts st h
runˢ-agree (K.H w ∷ C)        ts st h =
  runˢ-agree C (us ++ map wkᵀ ts) (K.stepH w st)
    (≈-++ {P = wkPoly (K.poly st)} {Q = mul-y₀ (½ ·ᴾ liftᴸ l)}
          (map wkᵀ ts) us (wk-≈ {P = K.poly st} ts h)
          (y₀-≈ {Q = ½ ·ᴾ liftᴸ l} (liftTerms ½ 1 l)
                (liftTerms-≈ ½ 1 l (Deg≤-H l))))
  where
  l  = K.sig st w
  us = map y₀ᵀ (liftTerms ½ 1 l)
runˢ-agree (K.CNOT c t _ ∷ C) ts st h =
  runˢ-agree C ts (K.stepCNOT c t st) h
runˢ-agree (K.R k w ∷ C)      ts st h =
  runˢ-agree C (us ++ ts) (K.stepR k w st)
    (≈-++ {P = K.poly st} {Q = pow (M ∸ k) ·ᴾ liftᴸ l} ts us h
          (liftTerms-≈ (pow (M ∸ k)) k l (Deg≤-R k l)))
  where
  l  = K.sig st w
  us = liftTerms (pow (M ∸ k)) k l
runˢ-agree (K.R† k w ∷ C)     ts st h =
  runˢ-agree C (us ++ ts) (K.stepR† k w st)
    (≈-≗ {P = K.poly st -ᴾ (pow (M ∸ k) ·ᴾ liftᴸ l)}
         {P′ = K.poly st +ᴾ ((- pow (M ∸ k)) ·ᴾ liftᴸ l)} (us ++ ts)
         (λ γ → cong (K.poly st γ +ℤ_)
                     (ℤP.neg-distribˡ-* (pow (M ∸ k)) (liftᴸ l γ)))
         (≈-++ {P = K.poly st} {Q = (- pow (M ∸ k)) ·ᴾ liftᴸ l} ts us h
               (liftTerms-≈ (- pow (M ∸ k)) k l (Deg≤-R† k l))))
  where
  l  = K.sig st w
  us = liftTerms (- pow (M ∸ k)) k l

-- A sparse state with its number of path variables denotes ξ when
-- that number is ξ's and the state represents ξ.

data Denotes {n k m : ℕ} (ξ : PathSum n k m) : ∃ (Rep n) → Set where
  denotes : (R : Rep n m) → Represents ξ R → Denotes ξ (m , R)

denotes-paths : {ξ : PathSum n k m} (p : ∃ (Rep n)) → Denotes ξ p →
                proj₁ p ≡ m
denotes-paths _ (denotes R r) = refl

denotes-represents : {ξ : PathSum n k m} (p : ∃ (Rep n))
                     (d : Denotes ξ p) →
                     Represents ξ (subst (Rep n) (denotes-paths p d) (proj₂ p))
denotes-represents _ (denotes R r) = r

-- The path-sum of a dense state, as PathSum.CRK.Circuit.⟦_⟧ builds it.

private
  psᵈ : (q : ∃ (K.State n)) → PathSum n k (proj₁ q)
  psᵈ q = ⟨ K.poly (proj₂ q) , (λ w → liftᴸ (K.sig (proj₂ q) w)) ⟩

  agree⇒denotes : (p : ∃ (Rep n)) (q : ∃ (K.State n)) → Agree p q →
                  Denotes (psᵈ {k = k} q) p
  agree⇒denotes _ _ (agree ts st h) =
    denotes (rep ts (K.sig st)) (h , λ w γ → refl)

-- The interpreter computes ⟦ C ⟧.

interpᴷ-agree : (C : K.Circuit n) → Agree (interpᴷ C) (K.run C K.init)
interpᴷ-agree {n} C = runˢ-agree C [] (K.init {n}) (λ γ → i∣0)

interpᴷ-correct : (C : K.Circuit n) → Denotes K.⟦ C ⟧ (interpᴷ C)
interpᴷ-correct C = agree⇒denotes {k = K.norm C} (interpᴷ C)
  (K.run C K.init) (interpᴷ-agree C)

interpᴷ-paths : (C : K.Circuit n) → proj₁ (interpᴷ C) ≡ K.paths C
interpᴷ-paths C = denotes-paths (interpᴷ C) (interpᴷ-correct C)

-- The same, as Sparse.Represents: the list sums to the phase of ⟦ C ⟧
-- modulo 2^M and the forms lift to its outputs.

interpᴷ-represents : (C : K.Circuit n) →
  Represents K.⟦ C ⟧ (subst (Rep n) (interpᴷ-paths C) (proj₂ (interpᴷ C)))
interpᴷ-represents C = denotes-represents (interpᴷ C) (interpᴷ-correct C)

interpᴷ-paths≤ : (C : K.Circuit n) → proj₁ (interpᴷ C) ≤ length C
interpᴷ-paths≤ C =
  ℕ.≤-trans (ℕ.≤-reflexive (interpᴷ-paths C)) (paths≤lengthᴷ C)


------------------------------------------------------------------------
-- The terms each gate produces

-- Exactly: Σ_{i ≤ k} C(s, i) for R_k and R_k† on a form of weight s,
-- s + 1 for H, none for CNOT.

stepRˢ-length : ∀ k (w : Fin n) (R : Rep n m) →
                length (terms (stepRˢ k w R)) ≡
                binomials (weight (forms R w)) k + length (terms R)
stepRˢ-length k w R = trans
  (List.length-++ (liftTerms (pow (M ∸ k)) k (forms R w)))
  (cong (_+ length (terms R))
        (liftTerms-length (pow (M ∸ k)) k (forms R w)))

stepR†ˢ-length : ∀ k (w : Fin n) (R : Rep n m) →
                 length (terms (stepR†ˢ k w R)) ≡
                 binomials (weight (forms R w)) k + length (terms R)
stepR†ˢ-length k w R = trans
  (List.length-++ (liftTerms (- pow (M ∸ k)) k (forms R w)))
  (cong (_+ length (terms R))
        (liftTerms-length (- pow (M ∸ k)) k (forms R w)))

stepHˢ-length : (w : Fin n) (R : Rep n m) →
                length (terms (stepHˢ w R)) ≡
                suc (weight (forms R w)) + length (terms R)
stepHˢ-length w R = trans
  (List.length-++ (map y₀ᵀ (liftTerms ½ 1 (forms R w))))
  (cong₂ _+_
    (trans (List.length-map y₀ᵀ (liftTerms ½ 1 (forms R w)))
      (trans (liftTerms-length ½ 1 (forms R w))
             (binomials-1 (weight (forms R w)))))
    (List.length-map wkᵀ (terms R)))

stepCNOTˢ-length : (c t : Fin n) (R : Rep n m) →
                   length (terms (stepCNOTˢ c t R)) ≡ length (terms R)
stepCNOTˢ-length c t R = refl

-- A bound on what a gate adds, in the number n + m of variables.

newTerms : K.Gate n → ℕ → ℕ
newTerms (K.H _)        v = suc v
newTerms (K.CNOT _ _ _) v = 0
newTerms (K.R k _)      v = suc v ^ k
newTerms (K.R† k _)     v = suc v ^ k

gate-length : (g : K.Gate n) (R : Rep n m) →
              length (terms (proj₂ (runˢ (g ∷ []) R))) ≤
              newTerms g (n + m) + length (terms R)
gate-length (K.H w)        R = ℕ.≤-trans
  (ℕ.≤-reflexive (stepHˢ-length w R))
  (ℕ.+-monoˡ-≤ (length (terms R)) (s≤s (weight≤ (forms R w))))
gate-length (K.CNOT c t _) R = ℕ.≤-refl
gate-length (K.R k w)      R = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-++ (liftTerms (pow (M ∸ k)) k (forms R w))))
  (ℕ.+-monoˡ-≤ (length (terms R))
    (liftTerms-length≤ (pow (M ∸ k)) k (forms R w)))
gate-length (K.R† k w)     R = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-++ (liftTerms (- pow (M ∸ k)) k (forms R w))))
  (ℕ.+-monoˡ-≤ (length (terms R))
    (liftTerms-length≤ (- pow (M ∸ k)) k (forms R w)))


------------------------------------------------------------------------
-- The terms in total

private
  -- The step of the induction below: a gate adding at most X terms
  -- to a state of a terms leaves one more gate's worth of room.
  step-bound : ∀ a a′ ℓ X → a′ ≤ X + a → a′ + ℓ * X ≤ a + suc ℓ * X
  step-bound a a′ ℓ X le = ℕ.≤-trans (ℕ.+-monoˡ-≤ (ℓ * X) le)
    (ℕ.≤-reflexive (trans (cong (_+ ℓ * X) (ℕ.+-comm X a))
                          (ℕ.+-assoc a X (ℓ * X))))

  -- x ≤ x^d for x, d ≥ 1.
  ≤-^ : ∀ x d → 1 ≤ d → suc x ≤ suc x ^ d
  ≤-^ x d 1≤d = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.^-identityʳ (suc x))))
                          (ℕ.^-monoʳ-≤ (suc x) 1≤d)

  -- A gate of degree at most d adds at most (N + 1)^d terms once
  -- n + m ≤ N.
  pow-≤ : ∀ {v N e d} → v ≤ N → e ≤ d → suc v ^ e ≤ suc N ^ d
  pow-≤ {v} {N} {e} {d} v≤N e≤d =
    ℕ.≤-trans (ℕ.^-monoˡ-≤ e (s≤s v≤N)) (ℕ.^-monoʳ-≤ (suc N) e≤d)

  le-H : ∀ n m c N → n + m + suc c ≤ N → n + suc m + c ≤ N
  le-H n m c N le = ℕ.≤-trans
    (ℕ.≤-reflexive (trans (cong (_+ c) (ℕ.+-suc n m))
                          (sym (ℕ.+-suc (n + m) c))))
    le

  le-nm : ∀ n m c N → n + m + c ≤ N → n + m ≤ N
  le-nm n m c N le = ℕ.≤-trans (ℕ.m≤m+n (n + m) c) le

-- With n + m + (Hadamards to come) ≤ N and level at most d ≥ 1, each
-- gate adds at most (N + 1)^d terms.

runˢ-length : (C : K.Circuit n) (R : Rep n m) (N d : ℕ) →
              n + m + K.norm C ≤ N → 1 ≤ d → K.level C ≤ d →
              length (terms (proj₂ (runˢ C R))) ≤
              length (terms R) + length C * suc N ^ d
runˢ-length []                 R N d le 1≤d lv =
  ℕ.m≤m+n (length (terms R)) 0
runˢ-length {n} {m} (K.H w ∷ C) R N d le 1≤d lv = ℕ.≤-trans
  (runˢ-length C (stepHˢ w R) N d (le-H n m (K.norm C) N le) 1≤d lv)
  (step-bound (length (terms R)) (length (terms (stepHˢ w R)))
    (length C) (suc N ^ d)
    (ℕ.≤-trans (gate-length (K.H w) R)
      (ℕ.+-monoˡ-≤ (length (terms R))
        (ℕ.≤-trans (s≤s (le-nm n m (suc (K.norm C)) N le))
                   (≤-^ N d 1≤d)))))
runˢ-length {n} {m} (K.CNOT c t _ ∷ C) R N d le 1≤d lv = ℕ.≤-trans
  (runˢ-length C (stepCNOTˢ c t R) N d le 1≤d lv)
  (step-bound (length (terms R)) (length (terms R)) (length C)
    (suc N ^ d) (ℕ.m≤n+m (length (terms R)) (suc N ^ d)))
runˢ-length {n} {m} (K.R k w ∷ C) R N d le 1≤d lv = ℕ.≤-trans
  (runˢ-length C (stepRˢ k w R) N d le 1≤d
    (ℕ.m⊔n≤o⇒n≤o k (K.level C) lv))
  (step-bound (length (terms R)) (length (terms (stepRˢ k w R)))
    (length C) (suc N ^ d)
    (ℕ.≤-trans (gate-length (K.R k w) R)
      (ℕ.+-monoˡ-≤ (length (terms R))
        (pow-≤ (le-nm n m (K.norm C) N le)
               (ℕ.m⊔n≤o⇒m≤o k (K.level C) lv)))))
runˢ-length {n} {m} (K.R† k w ∷ C) R N d le 1≤d lv = ℕ.≤-trans
  (runˢ-length C (stepR†ˢ k w R) N d le 1≤d
    (ℕ.m⊔n≤o⇒n≤o k (K.level C) lv))
  (step-bound (length (terms R)) (length (terms (stepR†ˢ k w R)))
    (length C) (suc N ^ d)
    (ℕ.≤-trans (gate-length (K.R† k w) R)
      (ℕ.+-monoˡ-≤ (length (terms R))
        (pow-≤ (le-nm n m (K.norm C) N le)
               (ℕ.m⊔n≤o⇒m≤o k (K.level C) lv)))))

-- From the start: at most |C| (n + |C| + 1)^max(1,k) terms.

private
  le-init : ∀ n (C : K.Circuit n) → n + 0 + K.norm C ≤ n + length C
  le-init n C = ℕ.≤-trans
    (ℕ.≤-reflexive (cong (_+ K.norm C) (ℕ.+-identityʳ n)))
    (ℕ.+-monoʳ-≤ n (norm≤lengthᴷ C))

interpᴷ-length : (C : K.Circuit n) →
                 length (terms (proj₂ (interpᴷ C))) ≤
                 length C * suc (n + length C) ^ (1 ⊔ K.level C)
interpᴷ-length {n} C = runˢ-length C initˢ (n + length C) (1 ⊔ K.level C)
  (le-init n C) (ℕ.m≤m⊔n 1 (K.level C)) (ℕ.m≤n⊔m 1 (K.level C))

-- In a single power: at most (n + |C| + 1)^(max(1,k)+1) terms, as
-- |C| ≤ n + |C| + 1.

private
  ℓ≤X : ∀ n ℓ → ℓ ≤ suc (n + ℓ)
  ℓ≤X n ℓ = ℕ.≤-trans (ℕ.m≤n+m ℓ n) (ℕ.n≤1+n (n + ℓ))

interpᴷ-length-poly : (C : K.Circuit n) →
                      length (terms (proj₂ (interpᴷ C))) ≤
                      suc (n + length C) ^ suc (1 ⊔ K.level C)
interpᴷ-length-poly {n} C = ℕ.≤-trans (interpᴷ-length C)
  (ℕ.*-monoˡ-≤ (suc (n + length C) ^ (1 ⊔ K.level C))
               (ℓ≤X n (length C)))

-- Every intermediate state is bounded by the same polynomial in the
-- whole circuit.

level-prefix : (C D : K.Circuit n) → K.level C ≤ K.level (C ++ D)
level-prefix []                 D = z≤n
level-prefix (K.H w ∷ C)        D = level-prefix C D
level-prefix (K.CNOT c t _ ∷ C) D = level-prefix C D
level-prefix (K.R k w ∷ C)      D = ℕ.⊔-monoʳ-≤ k (level-prefix C D)
level-prefix (K.R† k w ∷ C)     D = ℕ.⊔-monoʳ-≤ k (level-prefix C D)

length-prefix : (C D : K.Circuit n) → length C ≤ length (C ++ D)
length-prefix C D = ℕ.≤-trans (ℕ.m≤m+n (length C) (length D))
                              (ℕ.≤-reflexive (sym (List.length-++ C)))

interpᴷ-prefix : (C D : K.Circuit n) →
  interpᴷ (C ++ D) ≡ runˢ D (proj₂ (interpᴷ C)) ×
  length (terms (proj₂ (interpᴷ C))) ≤
  length (C ++ D) * suc (n + length (C ++ D)) ^ (1 ⊔ K.level (C ++ D))
interpᴷ-prefix {n} C D = runˢ-++ C D initˢ , ℕ.≤-trans (interpᴷ-length C)
  (ℕ.*-mono-≤ (length-prefix C D)
    (pow-≤ (ℕ.+-monoʳ-≤ n (length-prefix C D))
           (ℕ.⊔-monoʳ-≤ 1 (level-prefix C D))))

-- The whole run: the number of terms of all the states it passes
-- through, the initial and the final one included.

traceˢ : K.Circuit n → Rep n m → ℕ
traceˢ []                 R = length (terms R)
traceˢ (K.H w ∷ C)        R = length (terms R) + traceˢ C (stepHˢ w R)
traceˢ (K.CNOT c t _ ∷ C) R =
  length (terms R) + traceˢ C (stepCNOTˢ c t R)
traceˢ (K.R k w ∷ C)      R = length (terms R) + traceˢ C (stepRˢ k w R)
traceˢ (K.R† k w ∷ C)     R = length (terms R) + traceˢ C (stepR†ˢ k w R)

private
  trace-step : ∀ a a′ ℓ X t → a′ ≤ X + a →
               t ≤ suc ℓ * (a′ + ℓ * X) →
               a + t ≤ suc (suc ℓ) * (a + suc ℓ * X)
  trace-step a a′ ℓ X t le tle = ℕ.+-mono-≤
    (ℕ.m≤m+n a (suc ℓ * X))
    (ℕ.≤-trans tle (ℕ.*-monoʳ-≤ (suc ℓ) (step-bound a a′ ℓ X le)))

  trace-[] : ∀ a → a ≤ 1 * (a + 0 * 0)
  trace-[] a = ℕ.≤-reflexive (sym (trans (ℕ.+-identityʳ (a + 0))
                                         (ℕ.+-identityʳ a)))

traceˢ-length : (C : K.Circuit n) (R : Rep n m) (N d : ℕ) →
                n + m + K.norm C ≤ N → 1 ≤ d → K.level C ≤ d →
                traceˢ C R ≤
                suc (length C) * (length (terms R) + length C * suc N ^ d)
traceˢ-length []                 R N d le 1≤d lv =
  trace-[] (length (terms R))
traceˢ-length {n} {m} (K.H w ∷ C) R N d le 1≤d lv =
  trace-step (length (terms R)) (length (terms (stepHˢ w R))) (length C)
    (suc N ^ d) (traceˢ C (stepHˢ w R))
    (ℕ.≤-trans (gate-length (K.H w) R)
      (ℕ.+-monoˡ-≤ (length (terms R))
        (ℕ.≤-trans (s≤s (le-nm n m (suc (K.norm C)) N le))
                   (≤-^ N d 1≤d))))
    (traceˢ-length C (stepHˢ w R) N d (le-H n m (K.norm C) N le) 1≤d lv)
traceˢ-length {n} {m} (K.CNOT c t _ ∷ C) R N d le 1≤d lv =
  trace-step (length (terms R)) (length (terms R)) (length C)
    (suc N ^ d) (traceˢ C (stepCNOTˢ c t R))
    (ℕ.m≤n+m (length (terms R)) (suc N ^ d))
    (traceˢ-length C (stepCNOTˢ c t R) N d le 1≤d lv)
traceˢ-length {n} {m} (K.R k w ∷ C) R N d le 1≤d lv =
  trace-step (length (terms R)) (length (terms (stepRˢ k w R)))
    (length C) (suc N ^ d) (traceˢ C (stepRˢ k w R))
    (ℕ.≤-trans (gate-length (K.R k w) R)
      (ℕ.+-monoˡ-≤ (length (terms R))
        (pow-≤ (le-nm n m (K.norm C) N le)
               (ℕ.m⊔n≤o⇒m≤o k (K.level C) lv))))
    (traceˢ-length C (stepRˢ k w R) N d le 1≤d
      (ℕ.m⊔n≤o⇒n≤o k (K.level C) lv))
traceˢ-length {n} {m} (K.R† k w ∷ C) R N d le 1≤d lv =
  trace-step (length (terms R)) (length (terms (stepR†ˢ k w R)))
    (length C) (suc N ^ d) (traceˢ C (stepR†ˢ k w R))
    (ℕ.≤-trans (gate-length (K.R† k w) R)
      (ℕ.+-monoˡ-≤ (length (terms R))
        (pow-≤ (le-nm n m (K.norm C) N le)
               (ℕ.m⊔n≤o⇒m≤o k (K.level C) lv))))
    (traceˢ-length C (stepR†ˢ k w R) N d le 1≤d
      (ℕ.m⊔n≤o⇒n≤o k (K.level C) lv))

interpᴷ-trace : (C : K.Circuit n) →
                traceˢ C (initˢ {n}) ≤
                suc (length C) *
                (length C * suc (n + length C) ^ (1 ⊔ K.level C))
interpᴷ-trace {n} C = traceˢ-length C initˢ (n + length C)
  (1 ⊔ K.level C) (le-init n C) (ℕ.m≤m⊔n 1 (K.level C))
  (ℕ.m≤n⊔m 1 (K.level C))

-- In a single power: (n + |C| + 1)^(max(1,k)+2).

interpᴷ-trace-poly : (C : K.Circuit n) →
                     traceˢ C (initˢ {n}) ≤
                     suc (n + length C) ^ suc (suc (1 ⊔ K.level C))
interpᴷ-trace-poly {n} C = ℕ.≤-trans (interpᴷ-trace C)
  (ℕ.*-mono-≤ (s≤s (ℕ.m≤n+m (length C) n))
    (ℕ.*-monoˡ-≤ (suc (n + length C) ^ (1 ⊔ K.level C))
                 (ℓ≤X n (length C))))


------------------------------------------------------------------------
-- The size in bits

-- A list of at most ℓ (n + ℓ + 1)^d terms over m ≤ ℓ path variables
-- takes at most 2 (n + ℓ + M + 1)^(d+2) bits with its forms.

size-bound-list : ∀ d ℓ (R : Rep n m) → m ≤ ℓ →
                  length (terms R) ≤ ℓ * suc (n + ℓ) ^ d →
                  size R ≤ 2 * suc (n + ℓ + M) ^ suc (suc d)
size-bound-list {n} {m} d ℓ R m≤ℓ len = ℕ.≤-trans
  (ℕ.+-mono-≤ terms≤ forms≤)
  (ℕ.≤-reflexive (sym twice))
  where
  B : ℕ
  B = suc (n + ℓ + M)

  nm≤ : n + m ≤ n + ℓ + M
  nm≤ = ℕ.≤-trans (ℕ.+-monoʳ-≤ n m≤ℓ) (ℕ.m≤m+n (n + ℓ) M)

  ℓ≤B : ℓ ≤ B
  ℓ≤B = ℕ.≤-trans (ℕ.m≤n+m ℓ n)
          (ℕ.≤-trans (ℕ.m≤m+n (n + ℓ) M) (ℕ.n≤1+n _))

  n≤B : n ≤ B
  n≤B = ℕ.≤-trans (ℕ.m≤m+n n ℓ)
          (ℕ.≤-trans (ℕ.m≤m+n (n + ℓ) M) (ℕ.n≤1+n _))

  bits≤ : n + m + M ≤ B
  bits≤ = ℕ.≤-trans (ℕ.+-monoˡ-≤ M (ℕ.+-monoʳ-≤ n m≤ℓ)) (ℕ.n≤1+n _)

  B≤ : B ≤ B ^ suc d
  B≤ = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.^-identityʳ B)))
                 (ℕ.^-monoʳ-≤ B {1} {suc d} (s≤s z≤n))

  terms≤ : length (terms R) * (n + m + M) ≤ B ^ suc (suc d)
  terms≤ = ℕ.≤-trans
    (ℕ.*-mono-≤ (ℕ.≤-trans len
                  (ℕ.*-mono-≤ ℓ≤B
                    (ℕ.^-monoˡ-≤ d (s≤s (ℕ.m≤m+n (n + ℓ) M)))))
                bits≤)
    (ℕ.≤-reflexive (ℕ.*-comm (B ^ suc d) B))

  forms≤ : n * suc (n + m) ≤ B ^ suc (suc d)
  forms≤ = ℕ.≤-trans (ℕ.*-mono-≤ n≤B (s≤s nm≤)) (ℕ.*-monoʳ-≤ B B≤)

  twice : 2 * B ^ suc (suc d) ≡ B ^ suc (suc d) + B ^ suc (suc d)
  twice = cong (λ z → B ^ suc (suc d) + z)
               (ℕ.+-identityʳ (B ^ suc (suc d)))

interpᴷ-size : (C : K.Circuit n) →
               size (proj₂ (interpᴷ C)) ≤
               2 * suc (n + length C + M) ^ suc (suc (1 ⊔ K.level C))
interpᴷ-size C = size-bound-list (1 ⊔ K.level C) (length C)
  (proj₂ (interpᴷ C)) (interpᴷ-paths≤ C) (interpᴷ-length C)

-- So is every intermediate state, in the whole circuit.

interpᴷ-prefix-size : (C D : K.Circuit n) →
  size (proj₂ (interpᴷ C)) ≤
  2 * suc (n + length (C ++ D) + M) ^ suc (suc (1 ⊔ K.level (C ++ D)))
interpᴷ-prefix-size C D = size-bound-list (1 ⊔ K.level (C ++ D))
  (length (C ++ D)) (proj₂ (interpᴷ C))
  (ℕ.≤-trans (interpᴷ-paths≤ C) (length-prefix C D))
  (proj₂ (interpᴷ-prefix C D))


------------------------------------------------------------------------
-- The degree of the terms

-- H's new terms have degree at most 2, R_k's at most k, and the old
-- ones keep theirs.

stepHˢ-small : ∀ d → 2 ≤ d → (w : Fin n) (R : Rep n m) → Small d R →
               Small d (stepHˢ w R)
stepHˢ-small {n} {m} d 2≤d w R small = AllP.++⁺
  (AllP.map⁺ {f = y₀ᵀ}
    (All.map {P = λ t → ∥ proj₁ t ∥ ≤ 1}
             {Q = λ t → ∥ proj₁ (y₀ᵀ t) ∥ ≤ d}
             (λ {t} → deg {t}) (liftTerms-small ½ 1 (forms R w))))
  (AllP.map⁺ {f = wkᵀ} small)
  where
  deg : ∀ {t : Term n m} → ∥ proj₁ t ∥ ≤ 1 → ∥ proj₁ (y₀ᵀ t) ∥ ≤ d
  deg {(α , β) , c} le = ℕ.≤-trans
    (ℕ.≤-reflexive (ℕ.+-suc ∣ α ∣ ∣ β ∣)) (ℕ.≤-trans (s≤s le) 2≤d)

stepRˢ-small : ∀ d k → k ≤ d → (w : Fin n) (R : Rep n m) → Small d R →
               Small d (stepRˢ k w R)
stepRˢ-small d k k≤d w R small = AllP.++⁺
  (All.map (λ le → ℕ.≤-trans le k≤d)
    (liftTerms-small (pow (M ∸ k)) k (forms R w)))
  small

stepR†ˢ-small : ∀ d k → k ≤ d → (w : Fin n) (R : Rep n m) → Small d R →
                Small d (stepR†ˢ k w R)
stepR†ˢ-small d k k≤d w R small = AllP.++⁺
  (All.map (λ le → ℕ.≤-trans le k≤d)
    (liftTerms-small (- pow (M ∸ k)) k (forms R w)))
  small

runˢ-small : (C : K.Circuit n) (R : Rep n m) (d : ℕ) → 2 ≤ d →
             K.level C ≤ d → Small d R → Small d (proj₂ (runˢ C R))
runˢ-small []                 R d 2≤d lv small = small
runˢ-small (K.H w ∷ C)        R d 2≤d lv small =
  runˢ-small C (stepHˢ w R) d 2≤d lv (stepHˢ-small d 2≤d w R small)
runˢ-small (K.CNOT c t _ ∷ C) R d 2≤d lv small =
  runˢ-small C (stepCNOTˢ c t R) d 2≤d lv small
runˢ-small (K.R k w ∷ C)      R d 2≤d lv small =
  runˢ-small C (stepRˢ k w R) d 2≤d (ℕ.m⊔n≤o⇒n≤o k (K.level C) lv)
    (stepRˢ-small d k (ℕ.m⊔n≤o⇒m≤o k (K.level C) lv) w R small)
runˢ-small (K.R† k w ∷ C)     R d 2≤d lv small =
  runˢ-small C (stepR†ˢ k w R) d 2≤d (ℕ.m⊔n≤o⇒n≤o k (K.level C) lv)
    (stepR†ˢ-small d k (ℕ.m⊔n≤o⇒m≤o k (K.level C) lv) w R small)

-- So every term of the result has degree at most max(2, k).

interpᴷ-small : (C : K.Circuit n) →
                Small (2 ⊔ K.level C) (proj₂ (interpᴷ C))
interpᴷ-small C = runˢ-small C initˢ (2 ⊔ K.level C)
  (ℕ.m≤m⊔n 2 (K.level C)) (ℕ.m≤n⊔m 2 (K.level C)) []


------------------------------------------------------------------------
-- Compaction

-- One coefficient per monomial of degree at most d, each the sum of
-- the list's coefficients on that monomial, modulo 2^M.

compact : ℕ → Rep n m → Rep n m
compact d R = rep (sparse d ⟦ terms R ⟧ˢ) (forms R)

-- A representation by terms of degree at most d stays one.

compact-represents : ∀ d (ξ : PathSum n k m) (R : Rep n m) → Small d R →
                     Represents ξ R → Represents ξ (compact d R)
compact-represents d ξ R small (P≈ , outs) =
  ≈-trans {P = phase ξ} {Q = ⟦ terms R ⟧ˢ}
          {R = ⟦ sparse d ⟦ terms R ⟧ˢ ⟧ˢ} P≈
    (sparse-≈ d ⟦ terms R ⟧ˢ
      (small-Deg≤ d ⟦ terms R ⟧ˢ (terms R) small
                  (≈-refl {P = ⟦ terms R ⟧ˢ}))) ,
  outs

compact-small : ∀ d (R : Rep n m) → Small d (compact d R)
compact-small d R = sparse-small d ⟦ terms R ⟧ˢ

compact-length : ∀ d (R : Rep n m) →
                 length (terms (compact d R)) ≤ suc (n + m) ^ d
compact-length d R = sparse-length d ⟦ terms R ⟧ˢ

denotes-compact : ∀ d {ξ : PathSum n k m} (p : ∃ (Rep n)) →
                  Denotes ξ p → Small d (proj₂ p) →
                  Denotes ξ (proj₁ p , compact d (proj₂ p))
denotes-compact d {ξ} _ (denotes R r) small =
  denotes (compact d R) (compact-represents d ξ R small r)

-- The interpreter's result, compacted at degree max(2, k).

compactᴷ : K.Circuit n → ∃ (Rep n)
compactᴷ C = proj₁ (interpᴷ C) , compact (2 ⊔ K.level C) (proj₂ (interpᴷ C))

compactᴷ-correct : (C : K.Circuit n) → Denotes K.⟦ C ⟧ (compactᴷ C)
compactᴷ-correct C = denotes-compact (2 ⊔ K.level C) (interpᴷ C)
  (interpᴷ-correct C) (interpᴷ-small C)

-- It is exactly the representation PathSum.Size reads off the dense
-- phase, repᴷ C: the residues depend on the phase only modulo 2^M.

agree-compact : ∀ d (p : ∃ (Rep n)) (q : ∃ (K.State n)) → Agree p q →
                (proj₁ p , compact d (proj₂ p)) ≡
                (proj₁ q , rep (sparse d (K.poly (proj₂ q)))
                               (K.sig (proj₂ q)))
agree-compact d _ _ (agree {m} ts st h) =
  cong (λ us → (m , rep us (K.sig st)))
       (sparse-cong d {P = ⟦ ts ⟧ˢ} {Q = K.poly st}
                    (≈-sym {P = K.poly st} {Q = ⟦ ts ⟧ˢ} h))

compactᴷ≡repᴷ : (C : K.Circuit n) → compactᴷ C ≡ (K.paths C , repᴷ C)
compactᴷ≡repᴷ C = agree-compact (2 ⊔ K.level C) (interpᴷ C)
  (K.run C K.init) (interpᴷ-agree C)

compactᴷ-small : (C : K.Circuit n) →
                 Small (2 ⊔ K.level C) (proj₂ (compactᴷ C))
compactᴷ-small C = compact-small (2 ⊔ K.level C) (proj₂ (interpᴷ C))

compactᴷ-length : (C : K.Circuit n) →
                  length (terms (proj₂ (compactᴷ C))) ≤
                  suc (n + length C) ^ (2 ⊔ K.level C)
compactᴷ-length {n} C = ℕ.≤-trans
  (compact-length (2 ⊔ K.level C) (proj₂ (interpᴷ C)))
  (ℕ.^-monoˡ-≤ (2 ⊔ K.level C) (s≤s (ℕ.+-monoʳ-≤ n (interpᴷ-paths≤ C))))

compactᴷ-size : (C : K.Circuit n) →
                size (proj₂ (compactᴷ C)) ≤
                2 * suc (n + length C + M) ^ suc (2 ⊔ K.level C)
compactᴷ-size C = size-bound (2 ⊔ K.level C) (length C)
  (proj₂ (compactᴷ C))
  (ℕ.≤-trans (s≤s z≤n) (ℕ.m≤m⊔n 2 (K.level C))) (interpᴷ-paths≤ C)
  (compact-length (2 ⊔ K.level C) (proj₂ (interpᴷ C)))


------------------------------------------------------------------------
-- Corollary 2.15, computed

corollary-2-15ᴷ-sparse : (C : K.Circuit n) →
  Denotes K.⟦ C ⟧ (interpᴷ C) ×
  length (terms (proj₂ (interpᴷ C))) ≤
    length C * suc (n + length C) ^ (1 ⊔ K.level C) ×
  size (proj₂ (interpᴷ C)) ≤
    2 * suc (n + length C + M) ^ suc (suc (1 ⊔ K.level C)) ×
  Denotes K.⟦ C ⟧ (compactᴷ C) ×
  Small (2 ⊔ K.level C) (proj₂ (compactᴷ C)) ×
  length (terms (proj₂ (compactᴷ C))) ≤
    suc (n + length C) ^ (2 ⊔ K.level C) ×
  size (proj₂ (compactᴷ C)) ≤
    2 * suc (n + length C + M) ^ suc (2 ⊔ K.level C)
corollary-2-15ᴷ-sparse C =
  interpᴷ-correct C , interpᴷ-length C , interpᴷ-size C ,
  compactᴷ-correct C , compactᴷ-small C , compactᴷ-length C ,
  compactᴷ-size C
