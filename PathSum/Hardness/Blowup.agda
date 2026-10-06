------------------------------------------------------------------------
-- Presentations of groups
--
-- Complete reductions of the reduction's path-sums for x₁ ∨ … ∨ x_n
-- have an odd output coefficient on every input monomial (Amy, QPL
-- 2018, section 4, footnote 2, and proposition 3.2)
--
-- Footnote 2 infers P = co-NP from unique normal forms together with
-- proposition 3.2's claim that normalising takes polynomial time.  On
-- the path-sums of the reduction the two cannot hold together, whatever
-- P and co-NP are, for a normaliser that writes its polynomials as
-- lists of terms, as the paper's tool does -- an argument whose count
-- and running time are in words.  This module proves the part of it
-- that is about path-sums; the plan of phase B is in the header of
-- PathSum.Hardness.Certificate.
--
-- The claim.  Let φ be a CNF formula whose value is the OR of its n
-- variables -- the single clause x₁ ∨ … ∨ x_n (orφ n), of size
-- ‖φ‖ = n + 1, is one.  Every reduct ξ′ of PathSum.Hardness.Prepared's
-- cleanPS φ without path variables has, in the polynomial of its
-- target output, an odd coefficient on every nonempty monomial over
-- the input variables (reduct-odd-coefficients): 2^n − 1 monomials, a
-- polynomial that no representation listing its terms can write in
-- fewer than 2^n − 1 terms.  Under PathSum.Expand.UniqueNormalForms
-- every irreducible reduct of cleanPS φ has no path variables
-- (PathSum.Hardness.Conditional.unique⇒no-paths), so every normal
-- form of cleanPS (orφ n) -- a path-sum with 4n + 8 path variables on
-- at most 4n + 6 wires (orφ-size) -- is such a ξ′
-- (unique⇒odd-on-inputs, unique⇒orφ): a normaliser listing the terms
-- of its polynomials would write down exponentially many of them, and
-- could not take polynomial time.
--
-- The proof.  Such a ξ′ computes the specification
-- |x⟩|a⟩|t⟩ ↦ |x⟩|a⟩|t ⊕ φ(x)⟩ (Conditional.reduct-outputs): the bit
-- its target output takes at x is x_t ⊕ φ(x).  At the inputs
-- |v⟩|0⟩|0⟩ the polynomial's value is the value, in the n input
-- variables, of its coefficients on the monomials over the inputs
-- (eval-ext0: every other monomial contains a variable set to 0), and
-- that value is odd exactly when v is not all 0.  Then Möbius
-- inversion modulo 2, in the style of PathSum.Mobius (split at the
-- head variable, P = P₀ + x₀ P₁): a multilinear polynomial whose
-- values are odd exactly off 0 -- the OR -- has P₀ of the same kind
-- and P₁ odd exactly at 0 -- the NOR; one whose values are the NOR has
-- both halves of the NOR's kind; so the NOR's polynomials have every
-- coefficient odd (nor-coefficients) and the OR's every coefficient
-- but the constant one (or-coefficients) -- the algebraic normal form
-- of x₁ ∨ … ∨ x_n, Σ_{S ≠ ∅} Π_{i ∈ S} x_i, read modulo 2.
--
-- What is not formalised.  The count itself: that there are 2^n − 1
-- nonempty subsets of n variables, and hence as many terms, is left in
-- words.  Whether normal-formᶠ does reduce cleanPS (orφ n) completely
-- when normal forms are not unique -- they are not -- is not decided
-- here; only reducts without path variables are shown large, and under
-- the hypothesis every normal form is one.  Proposition 3.2's time
-- bound is not refuted here: normal forms that keep path variables
-- can be small.  (PathSum.Ladder.Size refutes it without any
-- hypothesis, for a family whose every normal form has no path
-- variables.)  Nor are the representation and the time formalised:
-- "exponentially many terms" presumes polynomials written as lists of
-- terms (the paper's multilinear forms), and "cannot take polynomial
-- time" presumes a time model; a compact representation -- the lifted
-- Boolean expression of PathSum.Hardness's specification, of linear
-- size -- holds the same output polynomial.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hardness.Blowup (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _∨_; _xor_; if_then_else_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc; splitAt; _↑ʳ_)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ) renaming (_+_ to _+ℤ_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Properties using (length-map)
open import Data.Nat.Base using (zero; _+_; _*_; _≤_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (contradiction)

import Data.Fin.Properties as Fin
import Data.Sum.Base as Sum

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using (_[_≔_]; ≔-here)
open import PathSum.Base using (PathSum; out)
open import PathSum.Classical M₀ using (none)
open import PathSum.CRK.Path M₀ using (paths)
open import PathSum.Expand M₀ using (UniqueNormalForms)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Match M using (Irreducibleᶠ)
open import PathSum.Hardness M₀ using (circuit)
open import PathSum.Hardness.CNF using
  (Assignment; Literal; pos; neg; Clause; CNF; ⟦_⟧ᶜ; ⟦_⟧ᶠ; ⟦⟧ᶠ-cong;
   cnf; nodes; ‖_‖)
open import PathSum.Hardness.Conditional M₀ using
  (reduct-outputs; unique⇒no-paths; cleanPS-size)
open import PathSum.Hardness.Netlist using (wires; tgt; blank; blank-inp)
open import PathSum.Hardness.Prepared M₀ using (cleanPS)
open import PathSum.HiddenShift.Sign M₀ using (odd-+)
open import PathSum.Mobius using (evalˢ; eval-nested)
open import PathSum.Polynomial using (Poly; eval; sat; Σsub)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Properties using (Σsub-0; Σsub-cong)

private
  variable
    n k r : ℕ


------------------------------------------------------------------------
-- The OR of some bits, and nonempty subsets

orᵇ : (Fin k → Bool) → Bool
orᵇ {zero}  x = false
orᵇ {suc k} x = x zero ∨ orᵇ (λ i → x (suc i))

Nonempty : Subset k → Set
Nonempty []            = ⊥
Nonempty (inside  ∷ s) = ⊤
Nonempty (outside ∷ s) = Nonempty s


------------------------------------------------------------------------
-- Möbius inversion modulo 2 for the OR and the NOR

-- Splitting at the head variable, as in PathSum.Mobius.

private
  infixr 5 _◂_

  _◂_ : Bool → (Fin k → Bool) → Fin (suc k) → Bool
  (b ◂ x) zero    = b
  (b ◂ x) (suc i) = x i

  evalˢ-false : (f : Subset (suc k) → ℤ) (x : Fin k → Bool) →
                evalˢ f (false ◂ x) ≡ evalˢ (λ s → f (outside ∷ s)) x
  evalˢ-false {k} f x = trans
    (cong (_+ℤ evalˢ (λ s → f (outside ∷ s)) x) (Σsub-0 {k}))
    (+-identityˡ _)

  -- A xor with a known bit, undone.

  xor-solve : ∀ {a b c} → a xor b ≡ c → a ≡ c xor b
  xor-solve {true}  {true}  refl = refl
  xor-solve {true}  {false} refl = refl
  xor-solve {false} {true}  refl = refl
  xor-solve {false} {false} refl = refl

  -- The halves P₀ (head absent) and P₁ (head present) of f.

  half₀ half₁ : (Subset (suc k) → ℤ) → Subset k → ℤ
  half₀ f s = f (outside ∷ s)
  half₁ f s = f (inside ∷ s)

  -- The value at true ◂ x is that of P₁ plus that of P₀, by
  -- computation.

  odd-true : (f : Subset (suc k) → ℤ) (x : Fin k → Bool) →
             odd (evalˢ f (true ◂ x)) ≡
             odd (evalˢ (half₁ f) x) xor odd (evalˢ (half₀ f) x)
  odd-true f x = odd-+ (evalˢ (half₁ f) x) (evalˢ (half₀ f) x)

  -- If the values of f are the NOR, so are those of both halves.

  nor₀ : (f : Subset (suc k) → ℤ) →
         (∀ x → odd (evalˢ f x) ≡ not (orᵇ x)) →
         ∀ x → odd (evalˢ (half₀ f) x) ≡ not (orᵇ x)
  nor₀ f h x = trans (cong odd (sym (evalˢ-false f x))) (h (false ◂ x))

  nor₁ : (f : Subset (suc k) → ℤ) →
         (∀ x → odd (evalˢ f x) ≡ not (orᵇ x)) →
         ∀ x → odd (evalˢ (half₁ f) x) ≡ not (orᵇ x)
  nor₁ f h x =
    trans (xor-solve (trans (sym (odd-true f x)) (h (true ◂ x))))
          (nor₀ f h x)

  -- If the values of f are the OR, P₀'s are the OR and P₁'s the NOR.

  or₀ : (f : Subset (suc k) → ℤ) → (∀ x → odd (evalˢ f x) ≡ orᵇ x) →
        ∀ x → odd (evalˢ (half₀ f) x) ≡ orᵇ x
  or₀ f h x = trans (cong odd (sym (evalˢ-false f x))) (h (false ◂ x))

  or₁ : (f : Subset (suc k) → ℤ) → (∀ x → odd (evalˢ f x) ≡ orᵇ x) →
        ∀ x → odd (evalˢ (half₁ f) x) ≡ not (orᵇ x)
  or₁ f h x =
    trans (xor-solve (trans (sym (odd-true f x)) (h (true ◂ x))))
          (cong not (or₀ f h x))

-- A multilinear polynomial whose values are the NOR modulo 2 has every
-- coefficient odd ...

nor-coefficients : (f : Subset k → ℤ) →
                   (∀ x → odd (evalˢ f x) ≡ not (orᵇ x)) →
                   ∀ s → odd (f s) ≡ true
nor-coefficients {zero}  f h []            = h (λ ())
nor-coefficients {suc k} f h (outside ∷ s) =
  nor-coefficients (half₀ f) (nor₀ f h) s
nor-coefficients {suc k} f h (inside  ∷ s) =
  nor-coefficients (half₁ f) (nor₁ f h) s

-- ... and one whose values are the OR has every coefficient odd but the
-- constant one.

or-coefficients : (f : Subset k → ℤ) → (∀ x → odd (evalˢ f x) ≡ orᵇ x) →
                  ∀ s → Nonempty s → odd (f s) ≡ true
or-coefficients {zero}  f h []            ()
or-coefficients {suc k} f h (outside ∷ s) ne =
  or-coefficients (half₀ f) (or₀ f h) s ne
or-coefficients {suc k} f h (inside  ∷ s) _  =
  nor-coefficients (half₁ f) (or₁ f h) s


------------------------------------------------------------------------
-- The first n variables, the others set to 0

-- An assignment of the first n of n + r variables, extended by 0.

ext0 : (Fin n → Bool) → Fin (n + r) → Bool
ext0 {n} v w = [ v , (λ _ → false) ]′ (splitAt n w)

private
  sat-cong : (s : Subset k) {x x′ : Fin k → Bool} →
             (∀ i → x i ≡ x′ i) → sat s x ≡ sat s x′
  sat-cong []            h = refl
  sat-cong (inside  ∷ s) h = cong₂ _∧_ (h zero) (sat-cong s (λ i → h (suc i)))
  sat-cong (outside ∷ s) h = sat-cong s (λ i → h (suc i))

  ext0-suc : (v : Fin (suc n) → Bool) (w : Fin (n + r)) →
             ext0 {suc n} {r} v (suc w) ≡ ext0 {n} {r} (λ i → v (suc i)) w
  ext0-suc {n} v w = go (splitAt n w)
    where
    go : (s : Fin n ⊎ Fin _) →
         [ v , (λ _ → false) ]′ (Sum.map₁ suc s) ≡
         [ (λ i → v (suc i)) , (λ _ → false) ]′ s
    go (inj₁ i) = refl
    go (inj₂ j) = refl

-- With every variable 0, only the empty monomial counts.

evalˢ-zeros : (g : Subset r → ℤ) →
              evalˢ g (λ _ → false) ≡ g (replicate r outside)
evalˢ-zeros {zero}  g = refl
evalˢ-zeros {suc r} g =
  trans (cong (_+ℤ evalˢ (λ s → g (outside ∷ s)) (λ _ → false)) (Σsub-0 {r}))
  (trans (+-identityˡ _) (evalˢ-zeros (λ s → g (outside ∷ s))))

-- So at ext0 v the value is that of the coefficients on the monomials
-- in the first n variables.

evalˢ-ext0 : (g : Subset (n + r) → ℤ) (v : Fin n → Bool) →
             evalˢ g (ext0 {n} {r} v) ≡
             evalˢ (λ s → g (s ++ replicate r outside)) v
evalˢ-ext0 {zero}      g v = evalˢ-zeros g
evalˢ-ext0 {suc n} {r} g v = cong₂ _+ℤ_ (head (v zero)) tail
  where
  v′ : Fin n → Bool
  v′ i = v (suc i)

  shifted : ∀ s → sat s (λ i → ext0 {suc n} {r} v (suc i)) ≡
                  sat s (ext0 {n} {r} v′)
  shifted s = sat-cong s (ext0-suc v)

  head : ∀ b →
         Σsub (λ s → if b ∧ sat s (λ i → ext0 {suc n} {r} v (suc i))
                     then g (inside ∷ s) else 0ℤ) ≡
         Σsub (λ s → if b ∧ sat s v′
                     then g (inside ∷ (s ++ replicate r outside)) else 0ℤ)
  head true  =
    trans (Σsub-cong (λ s → cong (λ c → if c then g (inside ∷ s) else 0ℤ)
                                 (shifted s)))
          (evalˢ-ext0 (λ s → g (inside ∷ s)) v′)
  head false = trans (Σsub-0 {n + r}) (sym (Σsub-0 {n}))

  tail : Σsub (λ s → if sat s (λ i → ext0 {suc n} {r} v (suc i))
                     then g (outside ∷ s) else 0ℤ) ≡
         Σsub (λ s → if sat s v′
                     then g (outside ∷ (s ++ replicate r outside)) else 0ℤ)
  tail =
    trans (Σsub-cong (λ s → cong (λ c → if c then g (outside ∷ s) else 0ℤ)
                                 (shifted s)))
          (evalˢ-ext0 (λ s → g (outside ∷ s)) v′)

-- A polynomial without path variables, likewise.

eval-ext0 : (P : Poly (n + r) 0) (v : Fin n → Bool) →
            eval P (ext0 {n} {r} v) none ≡
            evalˢ (λ s → P (s ++ replicate r outside , [])) v
eval-ext0 P v =
  trans (eval-nested P (ext0 v) none) (evalˢ-ext0 (λ α → P (α , [])) v)


------------------------------------------------------------------------
-- Reducts without path variables of cleanPS φ, when φ is the OR

-- The monomial of the input variables in s, on the wires of φ.

onInputs : (φ : CNF n) → Subset n → Subset (wires φ)
onInputs φ s = s ++ replicate (suc (nodes (cnf φ)) + 1) outside

private
  blank-tgt : (φ : CNF n) (v : Assignment n) →
              blank (nodes (cnf φ)) v (tgt φ) ≡ false
  blank-tgt {n} φ v =
    cong [ v , (λ _ → false) ]′
         (Fin.splitAt-↑ʳ n (suc (nodes (cnf φ)) + 1)
                         (suc (nodes (cnf φ)) ↑ʳ zero))

-- Every reduct of cleanPS φ without path variables has an odd
-- coefficient on every nonempty monomial over the inputs, in the
-- polynomial of its target output.

reduct-odd-coefficients :
  (φ : CNF n) → (∀ v → ⟦ φ ⟧ᶠ v ≡ orᵇ v) →
  ∀ {k′} (ξ′ : PathSum (wires φ) k′ 0) → cleanPS φ ⟶ᶠ* ξ′ →
  ∀ (s : Subset n) → Nonempty s →
  odd (out ξ′ (tgt φ) (onInputs φ s , [])) ≡ true
reduct-odd-coefficients {n} φ is-or ξ′ steps =
  or-coefficients (λ s → out ξ′ (tgt φ) (onInputs φ s , [])) values
  where
  sz : ℕ
  sz = nodes (cnf φ)

  values : ∀ v → odd (evalˢ (λ s → out ξ′ (tgt φ) (onInputs φ s , [])) v) ≡
                 orᵇ v
  values v =
    trans (cong odd (sym (eval-ext0 (out ξ′ (tgt φ)) v)))
    (trans (reduct-outputs φ ξ′ steps (blank sz v) (tgt φ))
    (trans (≔-here (blank sz v) (tgt φ) _)
           (cong₂ _xor_ (blank-tgt φ v)
                  (trans (⟦⟧ᶠ-cong φ (blank-inp sz v)) (is-or v)))))

-- It fails to be one only by keeping a path variable; under the
-- hypothesis of unique normal forms no irreducible reduct keeps one.

OddOnInputs : (φ : CNF n) → ∀ {k′ m′} → PathSum (wires φ) k′ m′ → Set
OddOnInputs {n} φ {m′ = zero}  ξ′ =
  ∀ (s : Subset n) → Nonempty s →
  odd (out ξ′ (tgt φ) (onInputs φ s , [])) ≡ true
OddOnInputs     φ {m′ = suc _} ξ′ = ⊥

unique⇒odd-on-inputs :
  UniqueNormalForms → (φ : CNF n) → (∀ v → ⟦ φ ⟧ᶠ v ≡ orᵇ v) →
  ∀ {k′ m′} (ξ′ : PathSum (wires φ) k′ m′) →
  cleanPS φ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ → OddOnInputs φ ξ′
unique⇒odd-on-inputs u φ is-or {m′ = zero}  ξ′ steps irr =
  reduct-odd-coefficients φ is-or ξ′ steps
unique⇒odd-on-inputs u φ is-or {m′ = suc _} ξ′ steps irr =
  contradiction (unique⇒no-paths u φ ξ′ steps irr) λ ()


------------------------------------------------------------------------
-- The single clause x₁ ∨ … ∨ x_n

shiftˡ : Literal n → Literal (suc n)
shiftˡ (pos v) = pos (suc v)
shiftˡ (neg v) = neg (suc v)

orClause : (n : ℕ) → Clause n
orClause zero    = []
orClause (suc n) = pos zero ∷ map shiftˡ (orClause n)

orφ : (n : ℕ) → CNF n
orφ n = orClause n ∷ []

private
  ⟦shift⟧ : (c : Clause n) (x : Assignment (suc n)) →
            ⟦ map shiftˡ c ⟧ᶜ x ≡ ⟦ c ⟧ᶜ (λ i → x (suc i))
  ⟦shift⟧ []          x = refl
  ⟦shift⟧ (pos v ∷ c) x = cong (x (suc v) ∨_) (⟦shift⟧ c x)
  ⟦shift⟧ (neg v ∷ c) x = cong (not (x (suc v)) ∨_) (⟦shift⟧ c x)

  ⟦orClause⟧ : (n : ℕ) (x : Assignment n) → ⟦ orClause n ⟧ᶜ x ≡ orᵇ x
  ⟦orClause⟧ zero    x = refl
  ⟦orClause⟧ (suc n) x = cong (x zero ∨_)
    (trans (⟦shift⟧ (orClause n) x) (⟦orClause⟧ n (λ i → x (suc i))))

  length-orClause : (n : ℕ) → length (orClause n) ≡ n
  length-orClause zero    = refl
  length-orClause (suc n) =
    cong suc (trans (length-map shiftˡ (orClause n)) (length-orClause n))

-- Its value is the OR, and its size n + 1.

⟦orφ⟧ : (n : ℕ) (x : Assignment n) → ⟦ orφ n ⟧ᶠ x ≡ orᵇ x
⟦orφ⟧ n x = trans (∧-identityʳ (⟦ orClause n ⟧ᶜ x)) (⟦orClause⟧ n x)

‖orφ‖ : (n : ℕ) → ‖ orφ n ‖ ≡ suc n
‖orφ‖ n =
  trans (cong (λ l → l + 0 + 1) (length-orClause n))
        (solve 1 (λ n → n :+ con 0 :+ con 1 := con 1 :+ n) refl n)

-- cleanPS (orφ n) has 4n + 8 path variables on at most 4n + 6 wires ...

orφ-size : (n : ℕ) → (paths (circuit (orφ n)) ≡ 4 * n + 8) ×
                     (wires (orφ n) ≤ 4 * n + 6)
orφ-size n =
  trans (proj₁ (cleanPS-size (orφ n)))
        (trans (cong (λ s → 4 * s + 4) (‖orφ‖ n))
               (solve 1 (λ n → con 4 :* (con 1 :+ n) :+ con 4
                               := con 4 :* n :+ con 8) refl n)) ,
  subst (wires (orφ n) ≤_)
        (trans (cong (λ s → n + 3 * s + 3) (‖orφ‖ n))
               (solve 1 (λ n → n :+ con 3 :* (con 1 :+ n) :+ con 3
                               := con 4 :* n :+ con 6) refl n))
        (proj₂ (proj₂ (cleanPS-size (orφ n))))

-- ... and every reduct of it without path variables, hence under the
-- hypothesis every normal form, has 2^n − 1 odd coefficients in its
-- target output.

orφ-reduct : (n : ℕ) → ∀ {k′} (ξ′ : PathSum (wires (orφ n)) k′ 0) →
             cleanPS (orφ n) ⟶ᶠ* ξ′ → ∀ (s : Subset n) → Nonempty s →
             odd (out ξ′ (tgt (orφ n)) (onInputs (orφ n) s , [])) ≡ true
orφ-reduct n = reduct-odd-coefficients (orφ n) (⟦orφ⟧ n)

unique⇒orφ : UniqueNormalForms → (n : ℕ) →
             ∀ {k′ m′} (ξ′ : PathSum (wires (orφ n)) k′ m′) →
             cleanPS (orφ n) ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ → OddOnInputs (orφ n) ξ′
unique⇒orφ u n = unique⇒odd-on-inputs u (orφ n) (⟦orφ⟧ n)
