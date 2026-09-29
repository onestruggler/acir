------------------------------------------------------------------------
-- Presentations of groups
--
-- Whether a sparse path-sum without path variables is the identity,
-- in the cost model (for Amy, QPL 2018, corollary 4.4)
--
-- Phase C of the plan in PathSum.Cost: corollaries 4.4 and 2.15 in
-- polynomial time, in the cost model.  Its design, in four modules:
--
--  * The final test (this module).  Corollary 4.4 ends when the
--    restricted path-sum of a circuit "reduces to |x⟩ ↦ |x⟩", and what
--    is left then has no path variables.  PathSum.Syntactic shows that
--    such a path-sum is the identity exactly when it has no
--    normalisation left, its outputs are the inputs modulo 2 and its
--    phase is 0 modulo 2^M, coefficient by coefficient (SyntacticId
--    below).  On a sparse representation all three are read off
--    directly: the normalisation is a number, each output is a
--    Z₂-linear form, which must be the form x_w itself (inputᶜ), and
--    the phase is a list of terms, whose sum vanishes modulo 2^M
--    exactly when the coefficient of every monomial occurring in it
--    does (phaseZeroᶜ; a monomial that occurs in no term has
--    coefficient 0 already).  idTestᶜ decides SyntacticId, for any
--    representation, canonical or not (idTest-correct), at a cost
--    polynomial in n and the number of terms.
--  * The restriction (PathSum.Cost.Restriction).  Section 4.1 reifies
--    the isometry restriction ξ|f(x,y)=x by Gaussian elimination; over
--    {H, S, CZ} it is reified during interpretation, as
--    PathSum.Circuit.⟦_⟧ᴿ does: a Hadamard puts x_w back on its wire
--    when no later Hadamard touches the wire.  The sparse interpreter
--    runs the circuit on a list of terms and a vector of the variables
--    on the wires, looking ahead along the rest of the circuit at each
--    Hadamard.  It computes a representation of ⟦ C ⟧ᴿ with exactly |C|
--    terms and at most |C| path variables, at a cost polynomial in
--    n + |C|.
--  * The decision (PathSum.Cost.Corollary), for circuits over
--    {H, S, CZ} only (the paper's {H, CNOT, R_k} at level ≤ 2 would
--    need a cost-annotated PathSum.Gauss, not done).  Interpret,
--    normalise at order 2 (PathSum.Cost.Normalise), and read the
--    verdict: with a
--    path variable left, the normal form is irreducible, internal and
--    of order 2, so lemma 4.3's progress (PathSum.Clifford.progress)
--    can only refute it, by lemma 4.2 or by a normalisation too small
--    for the rule the phase calls for, and the answer is no; with none
--    left, the final test decides.  Lemma 4.1 at the circuit
--    (PathSum.Corollary.lemma-4-1-circuit) carries the answer back to
--    ⟦ C ⟧.  The answer is true exactly when ⟦ C ⟧ ≋ idPS, and the cost
--    is at most an explicit polynomial in n + |C|, and in the volume
--    n · |C|.  Equivalence of two Clifford circuits goes through their
--    miter C₁ ++ C₂† (PathSum.Miter.miter), built in the monad too.
--  * The interpreter over {H, CNOT, R_k, R_k†}
--    (PathSum.Cost.Interpreter): PathSum.Size.Interpreter's gate by gate
--    construction written in the monad, with its value the same as the
--    pure interpreter's and its cost polynomial in n + |C| for fixed
--    k -- corollary 2.15's time half.
--
-- This module: the final test.  It is stated against the coefficient
-- criterion here, for every precision M; PathSum.Cost.Corollary turns
-- that into ≋ idPS at M = 3 + M₀ through PathSum.Syntactic.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.  Testing whether the normalisation is 0 is one
-- step, as for the other counters of the cost model.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Identity (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside; ⊥; ⁅_⁆; _∈_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈⁅y⁆⇒x≡y; ∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣⇒∣ᵤ)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Base using () renaming (_≡ᵇ_ to _≡ⁿ_)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; lookup; tabulate)
open import Data.Vec.Properties using
  (tabulate∘lookup; tabulate-cong; lookup-replicate; []=⇒lookup;
   lookup⇒[]=)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Cost
open import PathSum.Cost.Canon M using
  (coeffOfᶜ; value-coeffOfᶜ; cost-coeffOfᶜ)
open import PathSum.Cost.Coeff M using
  (0ᶠ; coeff-0ᶠ; isZero; isZero-true; isZeroᶜ; coeff-residue;
   residue-≡ᴹ; residue-0; ≡ᴹ-0; 0-≡ᴹ; ≡ᴹ-trans; ≡ᴹ-sym; ≡ᴹ-reflexive)
open import PathSum.Cost.Linear M using (liftXor-var)
open import PathSum.Cost.Monomial using
  (eqᶜ; value-eqᶜ; cost-eqᶜ; emptyᶜ; value-emptyᶜ; cost-emptyᶜ;
   singletonᶜ; value-singletonᶜ; cost-singletonᶜ)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Mon; Var; x[_]; y[_]; ⟪_⟫; 1ᵐ; _≟ᵐ_; μ; liftXor; 0ᴾ; _≈[_]_)
open import PathSum.Polynomial.Product using (monoᴾ; ≈-refl; ≈-sym; ≈-trans)
open import PathSum.Polynomial.Properties using
  (i∣0; _≡ᵇ_; ≡ᵇ⇒≡; ≡⇒≡ᵇ; emptyᵇ; emptyᵇ⇒≡⊥; emptyᵇ-⊥; liftXor-1ᵐ)
open import PathSum.Size M using (μ-lifted)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; residue; Rep; terms; forms; Represents)

import Data.Fin.Properties as Fin
import Data.Integer.Properties as ℤP
import Data.List.Relation.Unary.All as All
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    n m k : ℕ


------------------------------------------------------------------------
-- Small facts

private
  ∧-split : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-split true  b eq = refl , eq
  ∧-split false b ()

  not-true : ∀ c → not c ≡ true → c ≡ false
  not-true false _ = refl
  not-true true  ()

  -- 2 divides neither 1 nor -1.

  odd-1 : ¬ ((+ 2) ∣ 1ℤ)
  odd-1 d with ∣1⇒≡1 (∣⇒∣ᵤ d)
  ... | ()

  odd-−1 : ¬ ((+ 2) ∣ (0ℤ -ℤ 1ℤ))
  odd-−1 d with ∣1⇒≡1 (∣⇒∣ᵤ d)
  ... | ()

  -- A residue is 0 exactly when 2^M divides the integer.

  isZero-0ᶠ : isZero 0ᶠ ≡ true
  isZero-0ᶠ = cong (_≡ⁿ 0) (ℤP.+-injective coeff-0ᶠ)

  residue-zero : ∀ z → pow M ∣ z → isZero (residue z) ≡ true
  residue-zero z d =
    trans (cong isZero (trans (residue-≡ᴹ (≡ᴹ-0 d)) residue-0)) isZero-0ᶠ

  residue-zero⁻ : ∀ z → isZero (residue z) ≡ true → pow M ∣ z
  residue-zero⁻ z eq = 0-≡ᴹ (≡ᴹ-trans (≡ᴹ-sym (coeff-residue z))
    (≡ᴹ-reflexive (isZero-true (residue z) eq)))

  -- The monic polynomials away from their monomial.

  mono-off : (δ γ : Mon n m) → δ ≢ γ → monoᴾ δ γ ≡ 0ℤ
  mono-off δ γ δ≢γ with γ ≟ᵐ δ
  ... | yes γ≡δ = contradiction (sym γ≡δ) δ≢γ
  ... | no  _   = refl

  μ-off : (v : Var n m) (γ : Mon n m) → γ ≢ ⟪ v ⟫ → μ v γ ≡ 0ℤ
  μ-off v γ γ≢ with γ ≟ᵐ ⟪ v ⟫
  ... | yes γ≡ = contradiction γ≡ γ≢
  ... | no  _  = refl

  μ-on : (v : Var n m) → μ v ⟪ v ⟫ ≡ 1ℤ
  μ-on v with ⟪ v ⟫ ≟ᵐ ⟪ v ⟫
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  μ-x-on : {i w : Fin n} → i ≡ w → μ {n} {m} x[ w ] ⟪ x[ i ] ⟫ ≡ 1ℤ
  μ-x-on {i = i} refl = μ-on x[ i ]


------------------------------------------------------------------------
-- The phase vanishes modulo 1

-- For a term of the list: whether the coefficient of its monomial in
-- the whole list is 0 modulo 2^M.  For the list: whether that holds of
-- every term.

zeroAtᶜ : List (Term n m) → Term n m → Cost Bool
zeroAtᶜ ts t = coeffOfᶜ ts (proj₁ t) >>= isZeroᶜ

phaseZeroᶜ : List (Term n m) → Cost Bool
phaseZeroᶜ ts = allᶜ (zeroAtᶜ ts) ts

value-zeroAtᶜ : (ts : List (Term n m)) (t : Term n m) →
                value (zeroAtᶜ ts t) ≡ isZero (residue (⟦ ts ⟧ˢ (proj₁ t)))
value-zeroAtᶜ ts t = cong isZero (value-coeffOfᶜ ts (proj₁ t))

-- A monomial that no term carries has coefficient 0.

⟦⟧ˢ-absent : (ts : List (Term n m)) (γ : Mon n m) →
             All (λ t → proj₁ t ≢ γ) ts → ⟦ ts ⟧ˢ γ ≡ 0ℤ
⟦⟧ˢ-absent []             γ []            = refl
⟦⟧ˢ-absent ((δ , c) ∷ ts) γ (δ≢γ ∷ rest) = cong₂ _+ℤ_
  (trans (cong (coeff c *ℤ_) (mono-off δ γ δ≢γ)) (ℤP.*-zeroʳ (coeff c)))
  (⟦⟧ˢ-absent ts γ rest)

-- Every monomial either satisfies a property that every term's
-- monomial satisfies, or is carried by no term.

covered : {Z : Mon n m → Set} (us : List (Term n m)) →
          All (λ t → Z (proj₁ t)) us → (γ : Mon n m) →
          Z γ ⊎ All (λ t → proj₁ t ≢ γ) us
covered []       []       γ = inj₂ []
covered {Z = Z} (t ∷ us) (z ∷ zs) γ with proj₁ t ≟ᵐ γ
... | yes eq = inj₁ (subst Z eq z)
... | no  ne with covered {Z = Z} us zs γ
...   | inj₁ zγ  = inj₁ zγ
...   | inj₂ abs = inj₂ (ne ∷ abs)

-- The test is sound and complete.

phaseZero-sound : (ts : List (Term n m)) → value (phaseZeroᶜ ts) ≡ true →
                  ⟦ ts ⟧ˢ ≈[ pow M ] 0ᴾ
phaseZero-sound ts eq γ =
  subst (pow M ∣_) (sym (ℤP.+-identityʳ (⟦ ts ⟧ˢ γ)))
        (by (covered {Z = λ δ → pow M ∣ ⟦ ts ⟧ˢ δ} ts each γ))
  where
  each : All (λ t → pow M ∣ ⟦ ts ⟧ˢ (proj₁ t)) ts
  each = All.map (λ {t} e → residue-zero⁻ (⟦ ts ⟧ˢ (proj₁ t))
                              (trans (sym (value-zeroAtᶜ ts t)) e))
    (all-true (λ t → value (zeroAtᶜ ts t)) ts
              (trans (sym (value-allᶜ (zeroAtᶜ ts) ts)) eq))

  by : (pow M ∣ ⟦ ts ⟧ˢ γ) ⊎ All (λ t → proj₁ t ≢ γ) ts →
       pow M ∣ ⟦ ts ⟧ˢ γ
  by (inj₁ d)   = d
  by (inj₂ abs) = subst (pow M ∣_) (sym (⟦⟧ˢ-absent ts γ abs)) i∣0

phaseZero-complete : (ts : List (Term n m)) → ⟦ ts ⟧ˢ ≈[ pow M ] 0ᴾ →
                     value (phaseZeroᶜ ts) ≡ true
phaseZero-complete ts h = trans (value-allᶜ (zeroAtᶜ ts) ts)
  (all-true⁻ (λ t → value (zeroAtᶜ ts t)) ts
    (All.universal (λ t → trans (value-zeroAtᶜ ts t)
      (residue-zero (⟦ ts ⟧ˢ (proj₁ t))
        (subst (pow M ∣_) (ℤP.+-identityʳ (⟦ ts ⟧ˢ (proj₁ t)))
               (h (proj₁ t)))))
      ts))

-- One pass over the list per term: at most L (L (n + m + 2) + 2).

cost-phaseZeroᶜ : (ts : List (Term n m)) →
                  cost (phaseZeroᶜ ts) ≤
                  length ts * suc (length ts * suc (suc (n + m)) + 1)
cost-phaseZeroᶜ ts = cost-allᶜ (zeroAtᶜ ts) ts
  (λ t → ℕ.+-mono-≤ (cost-coeffOfᶜ ts (proj₁ t)) ℕ.≤-refl)


------------------------------------------------------------------------
-- An output is its input

-- Whether the form c ⊕ ⨁S is the variable x_w: c is 0, the inputs of
-- S are exactly w, and S has no path variable.

inputᶜ : Fin n → Lin n m → Cost Bool
inputᶜ w (c , (α , β)) = do
  s ← singletonᶜ w
  a ← eqᶜ α s
  e ← emptyᶜ β
  step (not c ∧ (a ∧ e))

value-inputᶜ : (w : Fin n) (c : Bool) (α : Subset n) (β : Subset m) →
               value (inputᶜ w (c , (α , β))) ≡
               not c ∧ ((α ≡ᵇ ⁅ w ⁆) ∧ emptyᵇ β)
value-inputᶜ w c α β = cong₂ (λ a e → not c ∧ (a ∧ e))
  (trans (value-eqᶜ α (value (singletonᶜ w)))
         (cong (α ≡ᵇ_) (value-singletonᶜ w)))
  (value-emptyᶜ β)

cost-inputᶜ : (w : Fin n) (l : Lin n m) → cost (inputᶜ w l) ≤ n + (n + (m + 1))
cost-inputᶜ w (c , (α , β)) = ℕ.+-mono-≤ (cost-singletonᶜ w)
  (ℕ.+-mono-≤ (cost-eqᶜ α (value (singletonᶜ w)))
    (ℕ.+-mono-≤ (cost-emptyᶜ β) ℕ.≤-refl))

-- When it passes, the form is x_w, whose lifting is μ x_w.

input-sound : (w : Fin n) (l : Lin n m) → value (inputᶜ w l) ≡ true →
              l ≡ varᴸ x[ w ]
input-sound w (c , (α , β)) eq = cong₂ _,_ (not-true c c≡)
  (cong₂ _,_ (≡ᵇ⇒≡ α ⁅ w ⁆ α≡) (emptyᵇ⇒≡⊥ β β≡))
  where
  parts = ∧-split (not c) ((α ≡ᵇ ⁅ w ⁆) ∧ emptyᵇ β)
                  (trans (sym (value-inputᶜ w c α β)) eq)
  c≡ = proj₁ parts
  α≡ = proj₁ (∧-split (α ≡ᵇ ⁅ w ⁆) (emptyᵇ β) (proj₂ parts))
  β≡ = proj₂ (∧-split (α ≡ᵇ ⁅ w ⁆) (emptyᵇ β) (proj₂ parts))

input-lift : (w : Fin n) (l : Lin n m) → l ≡ varᴸ x[ w ] →
             liftᴸ l ≈[ + 2 ] μ x[ w ]
input-lift w l refl γ =
  subst (λ z → (+ 2) ∣ (z -ℤ μ x[ w ] γ)) (μ-lifted x[ w ] γ)
        (≈-refl {c = + 2} {P = μ x[ w ]} γ)

-- Conversely: an output congruent to x_w modulo 2 is the form x_w.  Its
-- constant is its coefficient at 1, and its variables are those whose
-- coefficient is odd.

private
  ⊥≢⁅⁆ : (w : Fin n) → ⊥ ≢ ⁅ w ⁆
  ⊥≢⁅⁆ w eq = ∉⊥ (subst (w ∈_) (sym eq) (x∈⁅x⁆ w))

  lookup-⁅⁆-off : (w i : Fin n) → i ≢ w → lookup ⁅ w ⁆ i ≡ outside
  lookup-⁅⁆-off w i i≢w with lookup ⁅ w ⁆ i in eq
  ... | true  = contradiction
                  (x∈⁅y⁆⇒x≡y w (lookup⇒[]= i ⁅ w ⁆ eq)) i≢w
  ... | false = refl

  -- The four cases of a coefficient 0 or 1 against 0 or 1, modulo 2.

  bit-1 : ∀ b → (+ 2) ∣ ((if b then 1ℤ else 0ℤ) -ℤ 1ℤ) → b ≡ true
  bit-1 true  _ = refl
  bit-1 false d = ⊥-elim (odd-−1 d)

  bit-0 : ∀ b → (+ 2) ∣ ((if b then 1ℤ else 0ℤ) -ℤ 0ℤ) → b ≡ false
  bit-0 false _ = refl
  bit-0 true  d = ⊥-elim (odd-1 d)

input-complete : (w : Fin n) (l : Lin n m) → liftᴸ l ≈[ + 2 ] μ x[ w ] →
                 value (inputᶜ w l) ≡ true
input-complete w (true , (α , β)) h = ⊥-elim (odd-1 (subst ((+ 2) ∣_)
  (cong₂ _-ℤ_ (liftXor-1ᵐ true (α , β))
              (μ-off x[ w ] 1ᵐ (λ eq → ⊥≢⁅⁆ w (cong proj₁ eq))))
  (h 1ᵐ)))
input-complete {n} {m} w (false , (α , β)) h = trans (value-inputᶜ w false α β)
  (cong₂ _∧_ refl
    (cong₂ _∧_ (trans (cong (_≡ᵇ ⁅ w ⁆) α≡) (≡⇒≡ᵇ ⁅ w ⁆))
               (trans (cong emptyᵇ β≡) (emptyᵇ-⊥ {m}))))
  where
  -- The coefficient at x_i is the bit of i in α, and at y_j the bit of
  -- j in β.
  at-x : ∀ i → (+ 2) ∣ ((if lookup α i then 1ℤ else 0ℤ) -ℤ μ x[ w ] ⟪ x[ i ] ⟫)
  at-x i = subst (λ z → (+ 2) ∣ (z -ℤ μ x[ w ] ⟪ x[ i ] ⟫))
                 (liftXor-var false (α , β) x[ i ]) (h ⟪ x[ i ] ⟫)

  at-y : ∀ j → (+ 2) ∣ ((if lookup β j then 1ℤ else 0ℤ) -ℤ μ x[ w ] ⟪ y[ j ] ⟫)
  at-y j = subst (λ z → (+ 2) ∣ (z -ℤ μ x[ w ] ⟪ y[ j ] ⟫))
                 (liftXor-var false (α , β) y[ j ]) (h ⟪ y[ j ] ⟫)

  -- The 0/1 coefficient of a bit.
  one : Bool → ℤ
  one b = if b then 1ℤ else 0ℤ

  α-bits : ∀ i → lookup α i ≡ lookup ⁅ w ⁆ i
  α-bits i with i Fin.≟ w
  ... | yes i≡w  = trans (bit-1 (lookup α i)
                           (subst (λ z → (+ 2) ∣ (one (lookup α i) -ℤ z))
                                  (μ-x-on i≡w) (at-x i)))
                         (sym (trans (cong (lookup ⁅ w ⁆) i≡w)
                                     ([]=⇒lookup (x∈⁅x⁆ w))))
  ... | no  i≢w  = trans (bit-0 (lookup α i)
                           (subst (λ z → (+ 2) ∣ (one (lookup α i) -ℤ z))
                                  (μ-off x[ w ] ⟪ x[ i ] ⟫
                                    (λ eq → i≢w (x∈⁅y⁆⇒x≡y w
                                      (subst (i ∈_) (cong proj₁ eq)
                                             (x∈⁅x⁆ i)))))
                                  (at-x i)))
                         (sym (lookup-⁅⁆-off w i i≢w))

  β-bits : ∀ j → lookup β j ≡ lookup (⊥ {m}) j
  β-bits j = trans (bit-0 (lookup β j)
                     (subst (λ z → (+ 2) ∣ (one (lookup β j) -ℤ z))
                            (μ-off x[ w ] ⟪ y[ j ] ⟫
                              (λ eq → ⊥≢⁅⁆ w (cong proj₁ eq)))
                            (at-y j)))
                   (sym (lookup-replicate j outside))

  α≡ : α ≡ ⁅ w ⁆
  α≡ = trans (sym (tabulate∘lookup α))
             (trans (tabulate-cong α-bits) (tabulate∘lookup ⁅ w ⁆))

  β≡ : β ≡ ⊥
  β≡ = trans (sym (tabulate∘lookup β))
             (trans (tabulate-cong β-bits) (tabulate∘lookup (⊥ {m})))


------------------------------------------------------------------------
-- The identity test

-- Whether a natural number is 0.

zeroᵇ : ℕ → Bool
zeroᵇ zero    = true
zeroᵇ (suc _) = false

-- The criterion of PathSum.Syntactic: no normalisation, every output
-- the input modulo 2, and the phase 0 modulo 2^M, coefficient by
-- coefficient.

SyntacticId : PathSum n k 0 → Set
SyntacticId {n} {k} ψ =
  k ≡ 0 × (∀ w → out ψ w ≈[ + 2 ] μ x[ w ]) × phase ψ ≈[ pow M ] 0ᴾ

-- The test, on a representation with no path variables.

idTestᶜ : ℕ → Rep n 0 → Cost Bool
idTestᶜ k R = do
  a ← step (zeroᵇ k)
  b ← allFinᶜ (λ w → inputᶜ w (forms R w))
  c ← phaseZeroᶜ (terms R)
  pure (a ∧ (b ∧ c))

-- It decides the criterion for every path-sum the representation
-- stands for.

idTest-correct : (ψ : PathSum n k 0) (R : Rep n 0) → Represents ψ R →
                 (value (idTestᶜ k R) ≡ true ⇔ SyntacticId ψ)
idTest-correct {n} {k} ψ R (eqP , outs) = mk⇔ to from
  where
  b = value (allFinᶜ (λ w → inputᶜ w (forms R w)))
  c = value (phaseZeroᶜ (terms R))

  zeroᵇ-true : ∀ k → zeroᵇ k ≡ true → k ≡ 0
  zeroᵇ-true zero _ = refl

  zeroᵇ-0 : ∀ {k} → k ≡ 0 → zeroᵇ k ≡ true
  zeroᵇ-0 refl = refl

  lifted : ∀ w → out ψ w ≈[ + 2 ] μ x[ w ] →
           liftᴸ (forms R w) ≈[ + 2 ] μ x[ w ]
  lifted w h γ = subst (λ z → (+ 2) ∣ (z -ℤ μ x[ w ] γ)) (outs w γ) (h γ)

  unlifted : ∀ w → liftᴸ (forms R w) ≈[ + 2 ] μ x[ w ] →
             out ψ w ≈[ + 2 ] μ x[ w ]
  unlifted w h γ =
    subst (λ z → (+ 2) ∣ (z -ℤ μ x[ w ] γ)) (sym (outs w γ)) (h γ)

  to : value (idTestᶜ k R) ≡ true → SyntacticId ψ
  to eq = zeroᵇ-true k (proj₁ p₁) ,
          (λ w → unlifted w (input-lift w (forms R w)
                   (input-sound w (forms R w)
                     (allFinᶜ-true (λ w → inputᶜ w (forms R w))
                                   (proj₁ p₂) w)))) ,
          ≈-trans {P = phase ψ} {Q = ⟦ terms R ⟧ˢ} {R = 0ᴾ} eqP
                  (phaseZero-sound (terms R) (proj₂ p₂))
    where
    p₁ = ∧-split (zeroᵇ k) (b ∧ c) eq
    p₂ = ∧-split b c (proj₂ p₁)

  from : SyntacticId ψ → value (idTestᶜ k R) ≡ true
  from (k≡0 , outs′ , ph) = cong₂ _∧_ (zeroᵇ-0 k≡0)
    (cong₂ _∧_
      (allFinᶜ-complete (λ w → inputᶜ w (forms R w))
        (λ w → input-complete w (forms R w) (lifted w (outs′ w))))
      (phaseZero-complete (terms R)
        (≈-trans {P = ⟦ terms R ⟧ˢ} {Q = phase ψ} {R = 0ᴾ}
                 (≈-sym {P = phase ψ} {Q = ⟦ terms R ⟧ˢ} eqP) ph)))

-- Its cost: one step, then n forms and a pass over the terms per term.

cost-idTestᶜ : (k : ℕ) (R : Rep n 0) →
               cost (idTestᶜ k R) ≤
               1 + (n * suc (n + (n + 1)) +
                    (length (terms R) *
                       suc (length (terms R) * suc (suc (n + 0)) + 1) + 0))
cost-idTestᶜ {n} k R = s≤s (ℕ.+-mono-≤
  (cost-allFinᶜ (λ w → inputᶜ w (forms R w))
    (λ w → ℕ.≤-trans (cost-inputᶜ w (forms R w))
                     (ℕ.≤-reflexive (cong (λ z → n + (n + z)) refl))))
  (ℕ.+-mono-≤ (cost-phaseZeroᶜ (terms R)) ℕ.≤-refl))

-- In one power of n + L + 2, L the number of terms: at most
-- 6 (n + L + 2)^3.

private
  poly-bound : ∀ n L →
               1 + (n * suc (n + (n + 1)) +
                    (L * suc (L * suc (suc (n + 0)) + 1) + 0)) ≤
               6 * (2 + (n + L)) ^ 3
  poly-bound n L = ℕ.≤-trans
    (s≤s (ℕ.+-mono-≤ A≤ (ℕ.+-mono-≤ B≤ (z≤n {0}))))
    (ℕ.≤-trans (ℕ.≤-reflexive (expand Y))
      (ℕ.≤-trans (ℕ.+-monoʳ-≤ C (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ 2 sq≤)
                   (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ 2 lin≤) one≤)))
        (ℕ.≤-reflexive (trans (collect C) (cong (6 *_) cube)))))
    where
    Y = 2 + (n + L)
    C = Y * (Y * Y)

    n≤Y : n ≤ Y
    n≤Y = ℕ.≤-trans (ℕ.m≤m+n n L) (ℕ.m≤n+m (n + L) 2)

    L≤Y : L ≤ Y
    L≤Y = ℕ.≤-trans (ℕ.m≤n+m L n) (ℕ.m≤n+m (n + L) 2)

    n+2≤Y : suc (suc (n + 0)) ≤ Y
    n+2≤Y = s≤s (s≤s (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ n))
                                (ℕ.m≤m+n n L)))

    spread : suc (n + (n + 1)) ≡ n + suc (suc n)
    spread = solve 1 (λ n → con 1 :+ (n :+ (n :+ con 1)) :=
                            n :+ (con 2 :+ n)) refl n

    A≤ : n * suc (n + (n + 1)) ≤ Y * (Y + Y)
    A≤ = ℕ.*-mono-≤ n≤Y (ℕ.≤-trans (ℕ.≤-reflexive spread)
      (ℕ.+-mono-≤ n≤Y (s≤s (s≤s (ℕ.m≤m+n n L)))))

    B≤ : L * suc (L * suc (suc (n + 0)) + 1) ≤ Y * suc (Y * Y + 1)
    B≤ = ℕ.*-mono-≤ L≤Y (s≤s (ℕ.+-monoˡ-≤ 1 (ℕ.*-mono-≤ L≤Y n+2≤Y)))

    expand : ∀ Y → suc (Y * (Y + Y) + (Y * suc (Y * Y + 1) + 0)) ≡
                   Y * (Y * Y) + (2 * (Y * Y) + (2 * Y + 1))
    expand = solve 1 (λ Y → con 1 :+ (Y :* (Y :+ Y) :+
                              (Y :* (con 1 :+ (Y :* Y :+ con 1)) :+ con 0)) :=
                            Y :* (Y :* Y) :+ (con 2 :* (Y :* Y) :+
                              (con 2 :* Y :+ con 1))) refl

    sq≤ : Y * Y ≤ C
    sq≤ = ℕ.*-monoʳ-≤ Y (ℕ.m≤m*n Y Y)

    lin≤ : Y ≤ C
    lin≤ = ℕ.≤-trans (ℕ.m≤m*n Y Y) sq≤

    one≤ : 1 ≤ C
    one≤ = ℕ.≤-trans (s≤s z≤n) lin≤

    cube : C ≡ Y ^ 3
    cube = cong (λ z → Y * (Y * z)) (sym (ℕ.*-identityʳ Y))

    collect : ∀ C → C + (2 * C + (2 * C + C)) ≡ 6 * C
    collect = solve 1 (λ C → C :+ (con 2 :* C :+ (con 2 :* C :+ C)) :=
                             con 6 :* C) refl

cost-idTest-poly : (k : ℕ) (R : Rep n 0) →
                   cost (idTestᶜ k R) ≤ 6 * (2 + (n + length (terms R))) ^ 3
cost-idTest-poly {n} k R =
  ℕ.≤-trans (cost-idTestᶜ k R) (poly-bound n (length (terms R)))
