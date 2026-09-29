------------------------------------------------------------------------
-- Presentations of groups
--
-- A path variable on the sparse representation: its coefficients,
-- and removing it (for Amy, QPL 2018, figure 2 and lemma 4.3)
--
-- Every linear rule of figure 2 eliminates a path variable y_j: it
-- reads the quotient of the phase by y_j, P = y_j · Q + R, and the
-- reduct keeps R, with y_j gone and the later path variables
-- renumbered.  PathSum.Reorder writes this densely as P /ʸ j and
-- P ∖ʸ j: the coefficients of the monomials with y_j present, and with
-- it absent, over the remaining variables in their original order.
-- Here the same is computed on a sparse phase.
--
--  * quotᶜ j keeps the terms whose monomial contains y_j and removes
--    y_j from them (Vec.removeAt at j renumbers the rest); restᶜ j
--    does the same with the terms not containing it.  Their sums are,
--    coefficient by coefficient and exactly, the dense quotient and
--    rest (⟦quot⟧, ⟦rest⟧): the monomial (α , insertAt β j b) of the
--    old numbering is the monomial (α , β) of the new one.
--  * readᶜ reads a quotient's constant and its linear coefficients;
--    applied to quotᶜ j that is the coefficient of y_j itself and the
--    coefficients of its quadratic partners u · y_j (coeffsᶜ) -- what
--    the proof of lemma 4.3 decomposes as ¼a + ½bQ₀, and what the
--    rules match on.  Their values are the residues of the dense
--    quotient's coefficients (value-coeffsᶜ).
--  * The outputs are Z₂-linear forms (PathSum.Linear.Lin).  y_j is
--    absent from the outputs when no form contains it (formsFreeᶜ,
--    whose success gives the rules' premise NoVar (+ 2) y[ j ]), and
--    removing it renumbers each form (dropFormsᶜ): the lifting of the
--    renumbered form is, coefficient by coefficient, the part free of
--    y_j of the lifting of the form (drop-lift) -- setting y_j to 0 in
--    the lifting of c ⊕ ⨁S gives the lifting of c ⊕ ⨁(S ∖ y_j).
--
-- Each program costs one pass over its list (or over the n wires),
-- at most m + 3 steps per term (the lookup and the removal visit the
-- path bits), and readᶜ one pass per variable.  Costs are counted in
-- the cost model of PathSum.Cost: a cost model, not a machine model;
-- nothing is claimed about Turing machines or complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Split (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside; ∣_∣)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using
  (Vec; []; _∷_; lookup; insertAt; removeAt; tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using (head-part; tail-part)
open import PathSum.Cost
open import PathSum.Cost.Canon M using
  (coeffOfᶜ; value-coeffOfᶜ; cost-coeffOfᶜ; Ordᵀ)
open import PathSum.Cost.Coeff M using (Coeff; modᴹ; residue-≡ᴹ)
open import PathSum.Cost.Monomial using
  (removeAtᶜ; value-removeAtᶜ; cost-removeAtᶜ; oneᶜ; value-oneᶜ;
   cost-oneᶜ; varᶜ; value-varᶜ; cost-varᶜ)
open import PathSum.Linear using (Lin; liftᴸ)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; ⟪_⟫; 1ᵐ; ∥_∥; _≟ᵐ_; _⊆ᵐ?_; sgn; negpow;
   liftXor; NoVar; _∈ᵐ_; _≈[_]_)
open import PathSum.Polynomial.Product using (monoᴾ)
open import PathSum.Polynomial.Properties using
  (_≡ᵇ_; _⊆ᵇ_; _⊆ᵐᵇ_; emptyᵇ; emptyᵐ; ⌊≟ᵐ⌋; ⌊≟ᵐ1ᵐ⌋; ⌊⊆ᵐ?⌋; i∣0;
   liftXor-0)
open import PathSum.Order M using (pow; val)
open import PathSum.Reorder using (frontᴾ; _/ʸ_; _∖ʸ_; ∣insertAt∣)
open import PathSum.Size.Sparse M using (Term; coeff; ⟦_⟧ˢ; residue)

import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.Nat.Properties as ℕ
import Data.Vec.Properties as Vec

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- Splitting a list of terms at y_j

-- Whether a term contains y_j, and the term with y_j removed.

hasʸ : Fin (suc m) → Term n (suc m) → Bool
hasʸ j ((α , β) , a) = lookup β j

dropᵀ : Fin (suc m) → Term n (suc m) → Term n m
dropᵀ j ((α , β) , a) = (α , removeAt β j) , a

-- The quotient by y_j and the rest.

quot : Fin (suc m) → List (Term n (suc m)) → List (Term n m)
quot j ts = map (dropᵀ j) (keep (hasʸ j) ts)

rest : Fin (suc m) → List (Term n (suc m)) → List (Term n m)
rest j ts = map (dropᵀ j) (keep (λ t → not (hasʸ j t)) ts)

-- The programs.

hasᶜ : Fin (suc m) → Term n (suc m) → Cost Bool
hasᶜ j ((α , β) , a) = lookupᶜ β j

lacksᶜ : Fin (suc m) → Term n (suc m) → Cost Bool
lacksᶜ j t = do
  b ← hasᶜ j t
  step (not b)

dropᶜ : Fin (suc m) → Term n (suc m) → Cost (Term n m)
dropᶜ j ((α , β) , a) = (λ β′ → (α , β′) , a) <$> removeAtᶜ β j

quotᶜ : Fin (suc m) → List (Term n (suc m)) → Cost (List (Term n m))
quotᶜ j ts = do
  ks ← keepᶜ (hasᶜ j) ts
  mapᶜ (dropᶜ j) ks

restᶜ : Fin (suc m) → List (Term n (suc m)) → Cost (List (Term n m))
restᶜ j ts = do
  ks ← keepᶜ (lacksᶜ j) ts
  mapᶜ (dropᶜ j) ks

value-hasᶜ : (j : Fin (suc m)) (t : Term n (suc m)) →
             value (hasᶜ j t) ≡ hasʸ j t
value-hasᶜ j ((α , β) , a) = value-lookupᶜ β j

value-dropᶜ : (j : Fin (suc m)) (t : Term n (suc m)) →
              value (dropᶜ j t) ≡ dropᵀ j t
value-dropᶜ j ((α , β) , a) =
  cong (λ β′ → (α , β′) , a) (value-removeAtᶜ β j)

value-quotᶜ : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
              value (quotᶜ j ts) ≡ quot j ts
value-quotᶜ j ts = trans
  (value-mapᶜ (dropᶜ j) (value (keepᶜ (hasᶜ j) ts)))
  (trans (List.map-cong (value-dropᶜ j) (value (keepᶜ (hasᶜ j) ts)))
    (cong (map (dropᵀ j)) (trans (value-keepᶜ (hasᶜ j) ts)
                                 (keep-cong (value-hasᶜ j) ts))))

value-restᶜ : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
              value (restᶜ j ts) ≡ rest j ts
value-restᶜ j ts = trans
  (value-mapᶜ (dropᶜ j) (value (keepᶜ (lacksᶜ j) ts)))
  (trans (List.map-cong (value-dropᶜ j) (value (keepᶜ (lacksᶜ j) ts)))
    (cong (map (dropᵀ j)) (trans (value-keepᶜ (lacksᶜ j) ts)
      (keep-cong (λ t → cong not (value-hasᶜ j t)) ts))))

-- Neither is longer than the list.

length-quot : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
              length (quot j ts) ≤ length ts
length-quot j ts = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (dropᵀ j) (keep (hasʸ j) ts)))
  (keep-length (hasʸ j) ts)

length-rest : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
              length (rest j ts) ≤ length ts
length-rest j ts = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (dropᵀ j) (keep (λ t → not (hasʸ j t)) ts)))
  (keep-length (λ t → not (hasʸ j t)) ts)


------------------------------------------------------------------------
-- What the split stands for

-- Equality of bits.

infix 4 _==ᵇ_

_==ᵇ_ : Bool → Bool → Bool
true  ==ᵇ true  = true
false ==ᵇ false = true
true  ==ᵇ false = false
false ==ᵇ true  = false

==ᵇ-true : ∀ b → (b ==ᵇ true) ≡ b
==ᵇ-true true  = refl
==ᵇ-true false = refl

==ᵇ-false : ∀ b → (b ==ᵇ false) ≡ not b
==ᵇ-false true  = refl
==ᵇ-false false = refl

-- A monomial of the old numbering with bit b at j is one of the new
-- numbering with the bit removed.

insertAt-≡ᵇ : (β : Subset k) (j : Fin (suc k)) (b : Bool)
              (β₀ : Subset (suc k)) →
              (insertAt β j b ≡ᵇ β₀) ≡
              ((lookup β₀ j ==ᵇ b) ∧ (β ≡ᵇ removeAt β₀ j))
insertAt-≡ᵇ β zero inside  (inside  ∷ β₀) = refl
insertAt-≡ᵇ β zero inside  (outside ∷ β₀) = refl
insertAt-≡ᵇ β zero outside (inside  ∷ β₀) = refl
insertAt-≡ᵇ β zero outside (outside ∷ β₀) = refl
insertAt-≡ᵇ (inside  ∷ β) (suc j) b (inside  ∷ β₀@(_ ∷ _)) =
  insertAt-≡ᵇ β j b β₀
insertAt-≡ᵇ (inside  ∷ β) (suc j) b (outside ∷ β₀@(_ ∷ _)) =
  sym (∧-zeroʳ (lookup β₀ j ==ᵇ b))
insertAt-≡ᵇ (outside ∷ β) (suc j) b (inside  ∷ β₀@(_ ∷ _)) =
  sym (∧-zeroʳ (lookup β₀ j ==ᵇ b))
insertAt-≡ᵇ (outside ∷ β) (suc j) b (outside ∷ β₀@(_ ∷ _)) =
  insertAt-≡ᵇ β j b β₀

private
  ∧-if : ∀ (A E B : Bool) →
         (if A ∧ (E ∧ B) then 1ℤ else 0ℤ) ≡
         (if E then (if A ∧ B then 1ℤ else 0ℤ) else 0ℤ)
  ∧-if true  true  B = refl
  ∧-if true  false B = refl
  ∧-if false true  B = refl
  ∧-if false false B = refl

mono-insert : (α₀ : Subset n) (β₀ : Subset (suc m)) (α : Subset n)
              (β : Subset m) (j : Fin (suc m)) (b : Bool) →
              monoᴾ (α₀ , β₀) (α , insertAt β j b) ≡
              (if lookup β₀ j ==ᵇ b
               then monoᴾ (α₀ , removeAt β₀ j) (α , β) else 0ℤ)
mono-insert α₀ β₀ α β j b = trans
  (cong (λ x → if x then 1ℤ else 0ℤ)
    (trans (⌊≟ᵐ⌋ (α , insertAt β j b) (α₀ , β₀))
           (cong ((α ≡ᵇ α₀) ∧_) (insertAt-≡ᵇ β j b β₀))))
  (trans (∧-if (α ≡ᵇ α₀) (lookup β₀ j ==ᵇ b) (β ≡ᵇ removeAt β₀ j))
    (cong (λ x → if lookup β₀ j ==ᵇ b then (if x then 1ℤ else 0ℤ) else 0ℤ)
          (sym (⌊≟ᵐ⌋ (α , β) (α₀ , removeAt β₀ j)))))

-- The terms with bit b at j, renumbered, sum to the coefficients of
-- the monomials with bit b at j.

⟦split⟧ : (j : Fin (suc m)) (b : Bool) (ts : List (Term n (suc m)))
          (α : Subset n) (β : Subset m) →
          ⟦ map (dropᵀ j) (keep (λ t → hasʸ j t ==ᵇ b) ts) ⟧ˢ (α , β) ≡
          ⟦ ts ⟧ˢ (α , insertAt β j b)
⟦split⟧ j b []                     α β = refl
⟦split⟧ j b (((α₀ , β₀) , a) ∷ ts) α β = by (lookup β₀ j ==ᵇ b) refl
  where
  rest′ : List (Term _ _)
  rest′ = keep (λ t → hasʸ j t ==ᵇ b) ts

  by : ∀ e → (lookup β₀ j ==ᵇ b) ≡ e →
       ⟦ map (dropᵀ j) (if e then ((α₀ , β₀) , a) ∷ rest′ else rest′) ⟧ˢ
         (α , β) ≡
       coeff a *ℤ monoᴾ (α₀ , β₀) (α , insertAt β j b) +ℤ
       ⟦ ts ⟧ˢ (α , insertAt β j b)
  by true  eq = cong₂ _+ℤ_
    (cong (coeff a *ℤ_) (sym (trans (mono-insert α₀ β₀ α β j b)
      (cong (λ e → if e then monoᴾ (α₀ , removeAt β₀ j) (α , β) else 0ℤ)
            eq))))
    (⟦split⟧ j b ts α β)
  by false eq = trans (⟦split⟧ j b ts α β) (sym (trans
    (cong (λ z → coeff a *ℤ z +ℤ ⟦ ts ⟧ˢ (α , insertAt β j b))
      (trans (mono-insert α₀ β₀ α β j b)
        (cong (λ e → if e then monoᴾ (α₀ , removeAt β₀ j) (α , β) else 0ℤ)
              eq)))
    (trans (cong (_+ℤ ⟦ ts ⟧ˢ (α , insertAt β j b)) (ℤP.*-zeroʳ (coeff a)))
           (ℤP.+-identityˡ (⟦ ts ⟧ˢ (α , insertAt β j b))))))

-- So the quotient and the rest are exactly the dense ones.

⟦quot⟧ : (j : Fin (suc m)) (ts : List (Term n (suc m)))
         (α : Subset n) (β : Subset m) →
         ⟦ quot j ts ⟧ˢ (α , β) ≡ (⟦ ts ⟧ˢ /ʸ j) (α , β)
⟦quot⟧ j ts α β = trans
  (cong (λ us → ⟦ map (dropᵀ j) us ⟧ˢ (α , β))
        (keep-cong (λ t → sym (==ᵇ-true (hasʸ j t))) ts))
  (⟦split⟧ j true ts α β)

⟦rest⟧ : (j : Fin (suc m)) (ts : List (Term n (suc m)))
         (α : Subset n) (β : Subset m) →
         ⟦ rest j ts ⟧ˢ (α , β) ≡ (⟦ ts ⟧ˢ ∖ʸ j) (α , β)
⟦rest⟧ j ts α β = trans
  (cong (λ us → ⟦ map (dropᵀ j) us ⟧ˢ (α , β))
        (keep-cong (λ t → sym (==ᵇ-false (hasʸ j t))) ts))
  (⟦split⟧ j false ts α β)

-- Removing a bit that is outside keeps the degree.

∣removeAt∣-outside : (β₀ : Subset (suc k)) (j : Fin (suc k)) →
                     lookup β₀ j ≡ outside → ∣ removeAt β₀ j ∣ ≡ ∣ β₀ ∣
∣removeAt∣-outside β₀ j out = trans
  (sym (∣insertAt∣ (removeAt β₀ j) j outside))
  (cong ∣_∣ (trans (cong (insertAt (removeAt β₀ j) j) (sym out))
                   (Vec.insertAt-removeAt β₀ j)))


-- So a term of the rest keeps its degree, and its order bound.

rest-Ordᵀ : (d : ℕ) (j : Fin (suc m)) (ts : List (Term n (suc m))) →
            Ordᵀ d ts → Ordᵀ d (rest j ts)
rest-Ordᵀ d j []                     []       = []
rest-Ordᵀ d j (((α₀ , β₀) , a) ∷ ts) (h ∷ hs) = by (lookup β₀ j) refl
  where
  rest′ : List (Term _ _)
  rest′ = keep (λ t → not (hasʸ j t)) ts

  by : ∀ e → lookup β₀ j ≡ e →
       Ordᵀ d (map (dropᵀ j)
                   (if not e then ((α₀ , β₀) , a) ∷ rest′ else rest′))
  by true  eq = rest-Ordᵀ d j ts hs
  by false eq = subst (λ s → pow (val d (∣ α₀ ∣ + s)) ∣ coeff a)
                      (sym (∣removeAt∣-outside β₀ j eq)) h
              ∷ rest-Ordᵀ d j ts hs


------------------------------------------------------------------------
-- Reading a quotient

-- Its constant coefficient and the coefficient of each variable, as
-- residues.

Reading : ℕ → ℕ → Set
Reading n m = Coeff × (Vec Coeff n × Vec Coeff m)

reading : Poly n m → Reading n m
reading Q = residue (Q 1ᵐ)
          , (tabulate (λ i → residue (Q ⟪ x[ i ] ⟫))
          ,  tabulate (λ l → residue (Q ⟪ y[ l ] ⟫)))

reading-≗ : {P Q : Poly n m} → (∀ γ → P γ ≡ Q γ) → reading P ≡ reading Q
reading-≗ {P = P} {Q} h = cong₂ _,_ (cong residue (h _))
  (cong₂ _,_ (Vec.tabulate-cong (λ i → cong residue (h _)))
             (Vec.tabulate-cong (λ l → cong residue (h _))))

-- Residues read polynomials only modulo 2^M.

reading-≈ : {P Q : Poly n m} → P ≈[ pow M ] Q → reading P ≡ reading Q
reading-≈ {P = P} {Q} h = cong₂ _,_ (at 1ᵐ)
  (cong₂ _,_ (Vec.tabulate-cong (λ i → at ⟪ x[ i ] ⟫))
             (Vec.tabulate-cong (λ l → at ⟪ y[ l ] ⟫)))
  where
  at : ∀ γ → residue (P γ) ≡ residue (Q γ)
  at γ = residue-≡ᴹ {a = P γ} {b = Q γ} (modᴹ (h γ))

readᶜ : List (Term n m) → Cost (Reading n m)
readᶜ q = do
  o  ← oneᶜ
  c₀ ← coeffOfᶜ q o
  xs ← tabulateᶜ (λ i → varᶜ x[ i ] >>= coeffOfᶜ q)
  ys ← tabulateᶜ (λ l → varᶜ y[ l ] >>= coeffOfᶜ q)
  pure (c₀ , (xs , ys))

value-readᶜ : (q : List (Term n m)) → value (readᶜ q) ≡ reading ⟦ q ⟧ˢ
value-readᶜ {n} {m} q = cong₂ _,_
  (trans (value-coeffOfᶜ q (value (oneᶜ {n} {m})))
         (cong (λ γ → residue (⟦ q ⟧ˢ γ)) (value-oneᶜ {n} {m})))
  (cong₂ _,_
    (trans (value-tabulateᶜ (λ i → varᶜ x[ i ] >>= coeffOfᶜ q))
           (Vec.tabulate-cong (λ i → at x[ i ])))
    (trans (value-tabulateᶜ (λ l → varᶜ y[ l ] >>= coeffOfᶜ q))
           (Vec.tabulate-cong (λ l → at y[ l ]))))
  where
  at : (v : Var n m) →
       value (varᶜ v >>= coeffOfᶜ q) ≡ residue (⟦ q ⟧ˢ ⟪ v ⟫)
  at v = trans (value-coeffOfᶜ q (value (varᶜ v)))
               (cong (λ γ → residue (⟦ q ⟧ˢ γ)) (value-varᶜ v))

-- The coefficients of y_j: its own (the constant of the quotient) and
-- those of its quadratic partners u · y_j (the quotient's linear
-- coefficients).

coeffsᶜ : Fin (suc m) → List (Term n (suc m)) → Cost (Reading n m)
coeffsᶜ j ts = quotᶜ j ts >>= readᶜ

value-coeffsᶜ : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
                value (coeffsᶜ j ts) ≡ reading (⟦ ts ⟧ˢ /ʸ j)
value-coeffsᶜ j ts = trans (value-readᶜ (value (quotᶜ j ts)))
  (reading-≗ (λ γ → trans (cong (λ q → ⟦ q ⟧ˢ γ) (value-quotᶜ j ts))
                          (⟦quot⟧ j ts (proj₁ γ) (proj₂ γ))))


------------------------------------------------------------------------
-- The outputs

-- Whether y_j is absent from a form, and from every output.

freeᶜ : Fin (suc m) → Lin n (suc m) → Cost Bool
freeᶜ j (c , (α , β)) = do
  b ← lookupᶜ β j
  step (not b)

formsFreeᶜ : Fin (suc m) → (Fin n → Lin n (suc m)) → Cost Bool
formsFreeᶜ j f = allFinᶜ (λ w → freeᶜ j (f w))

-- If it is, y_j is absent from the lifting: every coefficient of a
-- monomial containing it is 0.

private
  not-true : ∀ b → not b ≡ true → b ≡ false
  not-true false _ = refl

freeᶜ-NoVar : (j : Fin (suc m)) (l : Lin n (suc m)) →
              value (freeᶜ j l) ≡ true → NoVar (+ 2) y[ j ] (liftᴸ l)
freeᶜ-NoVar j (c , (α , β)) eq γ j∈γ =
  subst ((+ 2) ∣_) (sym (liftXor-0 c (α , β) γ y[ j ] j∈γ j∉β)) i∣0
  where
  off : lookup β j ≡ false
  off = trans (sym (value-lookupᶜ β j)) (not-true _ eq)

  j∉β : ¬ (y[ j ] ∈ᵐ (α , β))
  j∉β j∈β with trans (sym (Vec.[]=⇒lookup j∈β)) off
  ... | ()

formsFreeᶜ-NoVar : (j : Fin (suc m)) (f : Fin n → Lin n (suc m)) →
                   value (formsFreeᶜ j f) ≡ true →
                   ∀ w → NoVar (+ 2) y[ j ] (liftᴸ (f w))
formsFreeᶜ-NoVar j f eq w =
  freeᶜ-NoVar j (f w) (allFinᶜ-true (λ w → freeᶜ j (f w)) eq w)

-- Removing y_j from a form.

dropForm : Fin (suc m) → Lin n (suc m) → Lin n m
dropForm j (c , (α , β)) = c , (α , removeAt β j)

dropFormᶜ : Fin (suc m) → Lin n (suc m) → Cost (Lin n m)
dropFormᶜ j (c , (α , β)) = (λ β′ → c , (α , β′)) <$> removeAtᶜ β j

dropFormsᶜ : Fin (suc m) → (Fin n → Lin n (suc m)) → Cost (Fin n → Lin n m)
dropFormsᶜ j f = lookup <$> tabulateᶜ (λ w → dropFormᶜ j (f w))

value-dropFormᶜ : (j : Fin (suc m)) (l : Lin n (suc m)) →
                  value (dropFormᶜ j l) ≡ dropForm j l
value-dropFormᶜ j (c , (α , β)) =
  cong (λ β′ → c , (α , β′)) (value-removeAtᶜ β j)

value-dropFormsᶜ : (j : Fin (suc m)) (f : Fin n → Lin n (suc m))
                   (w : Fin n) →
                   value (dropFormsᶜ j f) w ≡ dropForm j (f w)
value-dropFormsᶜ j f w = trans
  (cong (λ v → lookup v w) (value-tabulateᶜ (λ w → dropFormᶜ j (f w))))
  (trans (Vec.lookup∘tabulate (λ w → value (dropFormᶜ j (f w))) w)
         (value-dropFormᶜ j (f w)))

-- The lifting read through its Boolean tests.

liftXor-at : Bool → Bool → Bool → ℕ → ℤ
liftXor-at c e i s =
  if e then (if c then 1ℤ else 0ℤ)
  else (if i then sgn c *ℤ negpow (s ∸ 1) else 0ℤ)

liftXor-by : (c : Bool) (S γ : Mon n m) →
             liftXor c S γ ≡ liftXor-at c (emptyᵐ γ) (γ ⊆ᵐᵇ S) ∥ γ ∥
liftXor-by c S γ =
  cong₂ (λ e i → liftXor-at c e i ∥ γ ∥) (⌊≟ᵐ1ᵐ⌋ γ) (⌊⊆ᵐ?⌋ γ S)

-- Inserting a bit that is outside changes neither emptiness nor
-- inclusion in a set with that bit removed.

emptyᵇ-insertAt : (β : Subset k) (j : Fin (suc k)) →
                  emptyᵇ (insertAt β j outside) ≡ emptyᵇ β
emptyᵇ-insertAt β             zero    = refl
emptyᵇ-insertAt (inside  ∷ β) (suc j) = refl
emptyᵇ-insertAt (outside ∷ β) (suc j) = emptyᵇ-insertAt β j

insertAt-⊆ᵇ : (β : Subset k) (j : Fin (suc k)) (β₀ : Subset (suc k)) →
              (insertAt β j outside ⊆ᵇ β₀) ≡ (β ⊆ᵇ removeAt β₀ j)
insertAt-⊆ᵇ β             zero    (c ∷ β₀)               = refl
insertAt-⊆ᵇ (inside  ∷ β) (suc j) (inside  ∷ β₀@(_ ∷ _)) =
  insertAt-⊆ᵇ β j β₀
insertAt-⊆ᵇ (inside  ∷ β) (suc j) (outside ∷ β₀@(_ ∷ _)) = refl
insertAt-⊆ᵇ (outside ∷ β) (suc j) (c       ∷ β₀@(_ ∷ _)) =
  insertAt-⊆ᵇ β j β₀

-- The part free of y_j of the lifting of a form is the lifting of the
-- form with y_j removed.

drop-lift : (j : Fin (suc m)) (l : Lin n (suc m)) (α : Subset n)
            (β : Subset m) →
            tail-part (frontᴾ j (liftᴸ l)) (α , β) ≡
            liftᴸ (dropForm j l) (α , β)
drop-lift j (c , (αₗ , βₗ)) α β = trans
  (liftXor-by c (αₗ , βₗ) (α , insertAt β j outside))
  (trans
    (cong₂ (λ e i → liftXor-at c e i (∣ α ∣ + ∣ insertAt β j outside ∣))
           (cong (emptyᵇ α ∧_) (emptyᵇ-insertAt β j))
           (cong ((α ⊆ᵇ αₗ) ∧_) (insertAt-⊆ᵇ β j βₗ)))
    (trans
      (cong (λ s → liftXor-at c (emptyᵇ α ∧ emptyᵇ β)
                     ((α ⊆ᵇ αₗ) ∧ (β ⊆ᵇ removeAt βₗ j)) (∣ α ∣ + s))
            (∣insertAt∣ β j outside))
      (sym (liftXor-by c (αₗ , removeAt βₗ j) (α , β)))))


------------------------------------------------------------------------
-- Costs

cost-hasᶜ : (j : Fin (suc m)) (t : Term n (suc m)) → cost (hasᶜ j t) ≤ suc m
cost-hasᶜ j ((α , β) , a) = cost-lookupᶜ β j

cost-lacksᶜ : (j : Fin (suc m)) (t : Term n (suc m)) →
              cost (lacksᶜ j t) ≤ suc (suc m)
cost-lacksᶜ {m = m} j t = ℕ.≤-trans
  (ℕ.≤-reflexive (ℕ.+-comm (cost (hasᶜ j t)) 1))
  (s≤s (cost-hasᶜ j t))

cost-dropᶜ : (j : Fin (suc m)) (t : Term n (suc m)) → cost (dropᶜ j t) ≤ suc m
cost-dropᶜ j ((α , β) , a) = cost-removeAtᶜ β j

private
  twice : ∀ {a b c : ℕ} → a ≤ c → b ≤ c → a + b ≤ 2 * c
  twice {c = c} a≤ b≤ = ℕ.≤-trans (ℕ.+-mono-≤ a≤ b≤)
    (ℕ.≤-reflexive (cong (λ z → c + z) (sym (ℕ.+-identityʳ c))))

cost-quotᶜ : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
             cost (quotᶜ j ts) ≤ 2 * (length ts * (3 + m))
cost-quotᶜ {m = m} j ts = twice
  (ℕ.≤-trans (cost-keepᶜ (hasᶜ j) ts (cost-hasᶜ j))
             (ℕ.*-monoʳ-≤ (length ts) (ℕ.n≤1+n (2 + m))))
  (ℕ.≤-trans (cost-mapᶜ (dropᶜ j) ks (cost-dropᶜ j))
    (ℕ.*-mono-≤ (ℕ.≤-trans (ℕ.≤-reflexive
                  (cong length (trans (value-keepᶜ (hasᶜ j) ts)
                                      (keep-cong (value-hasᶜ j) ts))))
                  (keep-length (hasʸ j) ts))
                (ℕ.n≤1+n (2 + m))))
  where
  ks = value (keepᶜ (hasᶜ j) ts)

cost-restᶜ : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
             cost (restᶜ j ts) ≤ 2 * (length ts * (3 + m))
cost-restᶜ {m = m} j ts = twice
  (cost-keepᶜ (lacksᶜ j) ts (cost-lacksᶜ j))
  (ℕ.≤-trans (cost-mapᶜ (dropᶜ j) ks (cost-dropᶜ j))
    (ℕ.*-mono-≤ (ℕ.≤-trans (ℕ.≤-reflexive
                  (cong length (trans (value-keepᶜ (lacksᶜ j) ts)
                    (keep-cong (λ t → cong not (value-hasᶜ j t)) ts))))
                  (keep-length (λ t → not (hasʸ j t)) ts))
                (ℕ.n≤1+n (2 + m))))
  where
  ks = value (keepᶜ (lacksᶜ j) ts)

-- Reading a quotient of L terms over n + m = N variables: one pass
-- for the constant and one per variable, at most
-- (N + 1)(N + 1 + L (N + 2)).

cost-readᶜ : (q : List (Term n m)) →
             cost (readᶜ q) ≤
             suc (n + m) * (suc (n + m) + length q * (2 + (n + m)))
cost-readᶜ {n} {m} q = ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-oneᶜ {n} {m}) (ℕ.+-mono-≤ (cost-coeffOfᶜ q _)
    (ℕ.+-mono-≤ (cost-tabulateᶜ (λ i → varᶜ x[ i ] >>= coeffOfᶜ q)
                                (λ i → per x[ i ]))
      (ℕ.+-mono-≤ (cost-tabulateᶜ (λ l → varᶜ y[ l ] >>= coeffOfᶜ q)
                                  (λ l → per y[ l ]))
                  ℕ.≤-refl))))
  (ℕ.≤-trans (ℕ.m≤m+n _ 1) (ℕ.≤-reflexive (total n m X)))
  where
  X = length q * (2 + (n + m))

  per : (v : Var n m) → cost (varᶜ v >>= coeffOfᶜ q) ≤ (n + m) + X
  per v = ℕ.+-mono-≤ (cost-varᶜ v) (cost-coeffOfᶜ q (value (varᶜ v)))

  total : ∀ n m X →
          (n + m) + (X + (n * suc ((n + m) + X) +
                          (m * suc ((n + m) + X) + 0)))
          + 1 ≡ suc (n + m) * (suc (n + m) + X)
  total = solve 3 (λ n m X →
    (n :+ m) :+ (X :+ (n :* (con 1 :+ ((n :+ m) :+ X)) :+
                       (m :* (con 1 :+ ((n :+ m) :+ X)) :+ con 0)))
      :+ con 1 :=
    (con 1 :+ (n :+ m)) :* ((con 1 :+ (n :+ m)) :+ X)) refl

-- The coefficients of y_j cost a pass to split and the reading.

cost-coeffsᶜ : (j : Fin (suc m)) (ts : List (Term n (suc m))) →
               cost (coeffsᶜ j ts) ≤
               2 * (length ts * (3 + m)) +
               suc (n + m) * (suc (n + m) + length ts * (2 + (n + m)))
cost-coeffsᶜ {m} {n} j ts = ℕ.+-mono-≤ (cost-quotᶜ j ts)
  (ℕ.≤-trans (cost-readᶜ (value (quotᶜ j ts)))
    (ℕ.*-monoʳ-≤ (suc (n + m)) (ℕ.+-monoʳ-≤ (suc (n + m))
      (ℕ.*-monoˡ-≤ (2 + (n + m))
        (ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-quotᶜ j ts)))
                   (length-quot j ts))))))

-- The outputs: one lookup, or one removal, per wire.

cost-freeᶜ : (j : Fin (suc m)) (l : Lin n (suc m)) →
             cost (freeᶜ j l) ≤ suc (suc m)
cost-freeᶜ j (c , (α , β)) = ℕ.≤-trans
  (ℕ.≤-reflexive (ℕ.+-comm (cost (lookupᶜ β j)) 1))
  (s≤s (cost-lookupᶜ β j))

cost-formsFreeᶜ : (j : Fin (suc m)) (f : Fin n → Lin n (suc m)) →
                  cost (formsFreeᶜ j f) ≤ n * suc (suc (suc m))
cost-formsFreeᶜ j f =
  cost-allFinᶜ (λ w → freeᶜ j (f w)) (λ w → cost-freeᶜ j (f w))

cost-dropFormᶜ : (j : Fin (suc m)) (l : Lin n (suc m)) →
                 cost (dropFormᶜ j l) ≤ suc m
cost-dropFormᶜ j (c , (α , β)) = cost-removeAtᶜ β j

cost-dropFormsᶜ : (j : Fin (suc m)) (f : Fin n → Lin n (suc m)) →
                  cost (dropFormsᶜ j f) ≤ n * suc (suc m)
cost-dropFormsᶜ j f =
  cost-tabulateᶜ (λ w → dropFormᶜ j (f w)) (λ w → cost-dropFormᶜ j (f w))
