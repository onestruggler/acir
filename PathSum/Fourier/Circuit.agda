------------------------------------------------------------------------
-- Presentations of groups
--
-- The phase of a circuit has a Fourier expansion of linear size (Amy,
-- QPL 2018, section 2.2)
--
-- Section 2.2: "The phase polynomial could instead be represented in
-- linear space for any k by its Fourier expansion."  For circuits over
-- {H, CNOT, R_k, R_k†} (definition 2.9, PathSum.CRK.Circuit) this is
-- proved here, at the precision 2^M of the multilinear phase itself.
--
-- Every wire of the interpretation state holds a parity c ⊕ ⨁S, and
-- over this gate set the constant c stays 0 (Consts): CNOT adds two
-- such forms, a Hadamard puts a variable on its wire.  So the gates
-- add to the phase, at every point (CRK.Path's eval-R, eval-R†,
-- eval-H):
--
--   R_k on w     2^(M-k) [⨁S_w]                     one term,
--   R_k† on w    −2^(M-k) [⨁S_w]                    one term,
--   H on w       ½ [⨁S_w] y₀ = ¼ (y₀ + [⨁S_w] − [y₀ ⊕ ⨁S_w])
--                                                     three terms,
--   CNOT         nothing,
--
-- the identity 2ab = a + b − (a ⊕ b) for bits a, b (quarter-bits)
-- turning the Hadamard's product into parities; the old terms are read
-- with one more path variable (wkM).  Running a circuit tracks an
-- expansion with exactly cost C terms (track-run): three per
-- Hadamard, one per R_k or R_k†, none per CNOT -- at most 3|C|
-- (cost≤), and its value is the phase's at every point exactly
-- (circuit-fourier).
--
-- Circuits with X gates (PathSum.CRK.WithX, the gate set of section
-- 4's identity) are not covered: X negates the constant of a form, so
-- a phase gate on 1 ⊕ ⨁S contributes a constant and a negated parity,
-- and the invariant Consts above fails.  The same argument would go
-- through with the constant carried along, but it is not done here.
--
-- So the Fourier expansion of ⟦ C ⟧'s phase is linear in the circuit
-- for every level k, where the multilinear form has degree up to
-- max(2, k) and, for Clifford+T, can need cubically many terms
-- (PathSum.Size.Cubic).  As PathSum.Fourier says, the price is
-- uniqueness: these expansions are not unique modulo 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Fourier.Circuit (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside; outside; ⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-inverseʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (length-++; length-map)
open import Data.Nat.Base using (_≤_; _∸_; z≤n; s≤s)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)

import Data.Nat.Properties as ℕ
import Data.Fin.Properties as Fin

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase)
open import PathSum.CRK.Path M₀ using
  (Gate; H; CNOT; R; R†; Circuit; State; poly; sig; init; stepR; stepR†;
   stepCNOT; stepH; run; paths; ⟦_⟧; eval-R; eval-R†; eval-H)
open import PathSum.Cyclotomic M₀ using (extend)
open import PathSum.Fourier M₀ using
  (Expansion; Σᶠ; valueᶠ; sizeᶠ; FourierOf; valueᶠ-cong)
open import PathSum.Linear using (Lin; valᴸ; parᵐ; par; par-⊥; wkLin; varᴸ)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using (Mon; Poly; eval)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-cong; i∣0)
open import PathSum.Reduction M using (¼; ½)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- What each gate costs

cost : Circuit n → ℕ
cost []                = 0
cost (H _ ∷ C)         = 3 ℕ+ cost C
cost (CNOT _ _ _ ∷ C)  = cost C
cost (R _ _ ∷ C)       = suc (cost C)
cost (R† _ _ ∷ C)      = suc (cost C)

cost≤ : (C : Circuit n) → cost C ≤ 3 ℕ* length C
cost≤ []               = z≤n
cost≤ (H _ ∷ C)        = ℕ.≤-trans (ℕ.+-monoʳ-≤ 3 (cost≤ C))
  (ℕ.≤-reflexive (sym (ℕ.*-suc 3 (length C))))
cost≤ (CNOT _ _ _ ∷ C) = ℕ.≤-trans (cost≤ C) (ℕ.*-monoʳ-≤ 3 (ℕ.n≤1+n _))
cost≤ (R _ _ ∷ C)      = ℕ.≤-trans (s≤s (cost≤ C))
  (ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-trans (ℕ.n≤1+n _)
    (ℕ.≤-reflexive (sym (ℕ.*-suc 3 (length C))))))
cost≤ (R† _ _ ∷ C)     = ℕ.≤-trans (s≤s (cost≤ C))
  (ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-trans (ℕ.n≤1+n _)
    (ℕ.≤-reflexive (sym (ℕ.*-suc 3 (length C))))))


------------------------------------------------------------------------
-- Updating an expansion

private
  -- A term read with one more path variable, in front.

  wkM addM : Mon n m → Mon n (suc m)
  wkM  (α , β) = α , outside ∷ β
  addM (α , β) = α , inside ∷ β

  y₀M : Mon n (suc m)
  y₀M = ⊥ , inside ∷ ⊥

  wkT : ℤ × Mon n m → ℤ × Mon n (suc m)
  wkT (a , S) = a , wkM S

-- A Hadamard on a wire holding ⨁S, and a phase gate a · [⨁S].

hE : Mon n m → Expansion n m → Expansion n (suc m)
hE S (c , ts) =
  c , map wkT ts ++ (¼ , y₀M) ∷ (¼ , wkM S) ∷ (- ¼ , addM S) ∷ []

rE : ℤ → Mon n m → Expansion n m → Expansion n m
rE a S (c , ts) = c , ts ++ (a , S) ∷ []

private
  Σᶠ-++ : (ts us : List (ℤ × Mon n m)) (x : Fin n → Bool) (y : Fin m → Bool) →
          Σᶠ (ts ++ us) x y ≡ Σᶠ ts x y + Σᶠ us x y
  Σᶠ-++ []             us x y = sym (solve 1 (λ u → con 0ℤ :+ u := u) refl _)
  Σᶠ-++ ((a , S) ∷ ts) us x y = trans
    (cong (λ t → a * [ parᵐ S x y ]ᶻ + t) (Σᶠ-++ ts us x y))
    (solve 3 (λ p s u → p :+ (s :+ u) := (p :+ s) :+ u) refl
           (a * [ parᵐ S x y ]ᶻ) (Σᶠ ts x y) (Σᶠ us x y))

  Σᶠ-wk : (ts : List (ℤ × Mon n m)) (x : Fin n → Bool) (b : Bool)
          (g : Fin m → Bool) →
          Σᶠ (map wkT ts) x (extend b g) ≡ Σᶠ ts x g
  Σᶠ-wk []                   x b g = refl
  Σᶠ-wk ((a , (α , β)) ∷ ts) x b g =
    cong (λ t → a * [ par α x xor par β g ]ᶻ + t) (Σᶠ-wk ts x b g)

  -- The parities of the new terms.

  par-y₀ : (x : Fin n → Bool) (b : Bool) (g : Fin m → Bool) →
           parᵐ (y₀M {n} {m}) x (extend b g) ≡ b
  par-y₀ x b g = trans (cong₂ (λ p q → p xor (b xor q)) (par-⊥ x) (par-⊥ g))
                       (xor-false b)
    where
    xor-false : ∀ b → false xor (b xor false) ≡ b
    xor-false false = refl
    xor-false true  = refl

  par-add : (S : Mon n m) (x : Fin n → Bool) (b : Bool) (g : Fin m → Bool) →
            parᵐ (addM S) x (extend b g) ≡ b xor parᵐ S x g
  par-add (α , β) x b g = swap (par α x) b (par β g)
    where
    swap : ∀ p q r → p xor (q xor r) ≡ q xor (p xor r)
    swap false q r = refl
    swap true  false r = refl
    swap true  true  false = refl
    swap true  true  true  = refl

  -- 2ab = a + b − (a ⊕ b), at a quarter.

  ½≡¼+¼ : ½ ≡ ¼ + ¼
  ½≡¼+¼ = trans (pow-suc (suc M₀))
    (solve 1 (λ q → q :* con (+ 2) := q :+ q) refl ¼)

  quarter-bits : ∀ b p → ¼ * [ b ]ᶻ + (¼ * [ p ]ᶻ + (- ¼ * [ b xor p ]ᶻ + 0ℤ)) ≡
                         ½ * [ p ∧ b ]ᶻ
  quarter-bits b p =
    trans (shape b p) (cong (λ h → h * [ p ∧ b ]ᶻ) (sym ½≡¼+¼))
    where
    shape : ∀ b p → ¼ * [ b ]ᶻ + (¼ * [ p ]ᶻ + (- ¼ * [ b xor p ]ᶻ + 0ℤ)) ≡
                    (¼ + ¼) * [ p ∧ b ]ᶻ
    shape false false = solve 1 (λ q →
      q :* con 0ℤ :+ (q :* con 0ℤ :+ ((:- q) :* con 0ℤ :+ con 0ℤ)) :=
      (q :+ q) :* con 0ℤ) refl ¼
    shape false true  = solve 1 (λ q →
      q :* con 0ℤ :+ (q :* con 1ℤ :+ ((:- q) :* con 1ℤ :+ con 0ℤ)) :=
      (q :+ q) :* con 0ℤ) refl ¼
    shape true  false = solve 1 (λ q →
      q :* con 1ℤ :+ (q :* con 0ℤ :+ ((:- q) :* con 1ℤ :+ con 0ℤ)) :=
      (q :+ q) :* con 0ℤ) refl ¼
    shape true  true  = solve 1 (λ q →
      q :* con 1ℤ :+ (q :* con 1ℤ :+ ((:- q) :* con 0ℤ :+ con 0ℤ)) :=
      (q :+ q) :* con 1ℤ) refl ¼

-- The value of the updated expansions.

value-hE : (S : Mon n m) (E : Expansion n m) (x : Fin n → Bool) (b : Bool)
           (g : Fin m → Bool) →
           valueᶠ (hE S E) x (extend b g) ≡
           valueᶠ E x g + ½ * [ parᵐ S x g ∧ b ]ᶻ
value-hE S (c , ts) x b g = trans
  (cong (λ t → c + t)
    (trans (Σᶠ-++ (map wkT ts) ((¼ , y₀M) ∷ (¼ , wkM S) ∷ (- ¼ , addM S) ∷ [])
                  x (extend b g))
      (cong₂ _+_ (Σᶠ-wk ts x b g)
        (cong₂ (λ u v → ¼ * [ u ]ᶻ + (¼ * [ parᵐ S x g ]ᶻ +
                                     (- ¼ * [ v ]ᶻ + 0ℤ)))
               (par-y₀ x b g) (par-add S x b g)))))
  (trans (cong (λ t → c + (Σᶠ ts x g + t)) (quarter-bits b (parᵐ S x g)))
         (solve 3 (λ c s h → c :+ (s :+ h) := (c :+ s) :+ h) refl
                c (Σᶠ ts x g) (½ * [ parᵐ S x g ∧ b ]ᶻ)))

value-rE : (a : ℤ) (S : Mon n m) (E : Expansion n m) (x : Fin n → Bool)
           (y : Fin m → Bool) →
           valueᶠ (rE a S E) x y ≡ valueᶠ E x y + a * [ parᵐ S x y ]ᶻ
value-rE a S (c , ts) x y = trans
  (cong (λ t → c + t) (Σᶠ-++ ts ((a , S) ∷ []) x y))
  (solve 3 (λ c s t → c :+ (s :+ (t :+ con 0ℤ)) := (c :+ s) :+ t) refl
         c (Σᶠ ts x y) (a * [ parᵐ S x y ]ᶻ))


------------------------------------------------------------------------
-- Tracking a run

-- Every wire's form has constant 0.

Consts : State n m → Set
Consts {n} st = ∀ (w : Fin n) → proj₁ (sig st w) ≡ false

-- The expansion takes the phase's value at every point, exactly.

record Tracks {n m : ℕ} (st : State n m) (E : Expansion n m) : Set where
  field
    consts : Consts st
    values : ∀ x y → eval (poly st) x y ≡ valueᶠ E x y

open Tracks

private
  -- Along a wire with constant 0, the form's value is its parity.

  valᴸ-0 : (l : Lin n m) → proj₁ l ≡ false → ∀ x y →
           valᴸ l x y ≡ parᵐ (proj₂ l) x y
  valᴸ-0 (false , S) refl x y = refl
  valᴸ-0 (true  , S) ()   x y

  -- Redirecting a wire to a form with constant 0 keeps the constants 0.

  if-const : ∀ {u v : Lin n m} (d : Bool) → proj₁ u ≡ false →
             proj₁ v ≡ false → proj₁ (if d then u else v) ≡ false
  if-const true  eu ev = eu
  if-const false eu ev = ev

  ext-split : ∀ (y : Fin (suc m) → Bool) i → y i ≡ extend (y zero) (λ j → y (suc j)) i
  ext-split y zero    = refl
  ext-split y (suc i) = refl

track-H : (w : Fin n) {st : State n m} {E : Expansion n m} →
          Tracks st E → Tracks (stepH w st) (hE (proj₂ (sig st w)) E)
track-H {n} w {st} {E} t = record
  { consts = λ v → if-const ⌊ v Fin.≟ w ⌋ refl (consts t v)
  ; values = λ x y → trans
      (eval-cong (poly (stepH w st)) {x} {x} {y} {extend (y zero) (g y)}
                 (λ _ → refl) (ext-split y))
      (trans (eval-H w st x (y zero) (g y))
        (trans (cong₂ (λ e p → e + ½ * [ p ∧ y zero ]ᶻ)
                      (values t x (g y))
                      (valᴸ-0 (sig st w) (consts t w) x (g y)))
          (trans (sym (value-hE (proj₂ (sig st w)) E x (y zero) (g y)))
                 (valueᶠ-cong (hE (proj₂ (sig st w)) E) {x} {x}
                              {extend (y zero) (g y)} {y}
                              (λ _ → refl) (λ i → sym (ext-split y i))))))
  }
  where
  g : (Fin (suc _) → Bool) → Fin _ → Bool
  g y j = y (suc j)

track-CNOT : (c t : Fin n) {st : State n m} {E : Expansion n m} →
             Tracks st E → Tracks (stepCNOT c t st) E
track-CNOT c t {st} tr = record
  { consts = λ v → if-const ⌊ v Fin.≟ t ⌋
      (cong₂ _xor_ (consts tr t) (consts tr c)) (consts tr v)
  ; values = values tr
  }

track-R : (k : ℕ) (w : Fin n) {st : State n m} {E : Expansion n m} →
          Tracks st E →
          Tracks (stepR k w st) (rE (pow (M ∸ k)) (proj₂ (sig st w)) E)
track-R k w {st} {E} tr = record
  { consts = consts tr
  ; values = λ x y → trans (eval-R k w st x y)
      (trans (cong₂ (λ e p → e + pow (M ∸ k) * [ p ]ᶻ)
                    (values tr x y) (valᴸ-0 (sig st w) (consts tr w) x y))
             (sym (value-rE (pow (M ∸ k)) (proj₂ (sig st w)) E x y)))
  }

track-R† : (k : ℕ) (w : Fin n) {st : State n m} {E : Expansion n m} →
           Tracks st E →
           Tracks (stepR† k w st) (rE (- pow (M ∸ k)) (proj₂ (sig st w)) E)
track-R† k w {st} {E} tr = record
  { consts = consts tr
  ; values = λ x y → trans (eval-R† k w st x y)
      (trans (cong₂ (λ e p → e - pow (M ∸ k) * [ p ]ᶻ)
                    (values tr x y) (valᴸ-0 (sig st w) (consts tr w) x y))
        (trans (neg (valueᶠ E x y) (pow (M ∸ k))
                    [ parᵐ (proj₂ (sig st w)) x y ]ᶻ)
               (sym (value-rE (- pow (M ∸ k)) (proj₂ (sig st w)) E x y))))
  }
  where
  neg : ∀ e a p → e - a * p ≡ e + (- a) * p
  neg = solve 3 (λ e a p → e :- a :* p := e :+ (:- a) :* p) refl

-- Along a whole run, with exactly cost C new terms.

Tracked : ∃ (State n) → ℕ → Set
Tracked {n} p s =
  ∃ λ (E : Expansion n (proj₁ p)) → sizeᶠ E ≡ s × Tracks (proj₂ p) E

private
  size-hE : (S : Mon n m) (E : Expansion n m) → sizeᶠ (hE S E) ≡ sizeᶠ E ℕ+ 3
  size-hE S (c , ts) =
    trans (length-++ (map wkT ts) {(¼ , y₀M) ∷ (¼ , wkM S) ∷ (- ¼ , addM S) ∷ []})
          (cong (_ℕ+ 3) (length-map wkT ts))

  size-rE : (a : ℤ) (S : Mon n m) (E : Expansion n m) →
            sizeᶠ (rE a S E) ≡ sizeᶠ E ℕ+ 1
  size-rE a S (c , ts) = length-++ ts {(a , S) ∷ []}

track-run : (C : Circuit n) (st : State n m) (E : Expansion n m) →
            Tracks st E → Tracked (run C st) (sizeᶠ E ℕ+ cost C)
track-run []               st E tr = E , sym (ℕ.+-identityʳ (sizeᶠ E)) , tr
track-run (H w ∷ C)        st E tr
  with track-run C (stepH w st) (hE (proj₂ (sig st w)) E) (track-H w tr)
... | E′ , s , tr′ = E′ ,
  trans s (trans (cong (_ℕ+ cost C) (size-hE (proj₂ (sig st w)) E))
                 (ℕ.+-assoc (sizeᶠ E) 3 (cost C))) , tr′
track-run (CNOT c t _ ∷ C) st E tr = track-run C (stepCNOT c t st) E
  (track-CNOT c t tr)
track-run (R k w ∷ C)      st E tr
  with track-run C (stepR k w st) (rE (pow (M ∸ k)) (proj₂ (sig st w)) E)
                 (track-R k w tr)
... | E′ , s , tr′ = E′ ,
  trans s (trans (cong (_ℕ+ cost C) (size-rE (pow (M ∸ k)) (proj₂ (sig st w)) E))
                 (ℕ.+-assoc (sizeᶠ E) 1 (cost C))) , tr′
track-run (R† k w ∷ C)     st E tr
  with track-run C (stepR† k w st) (rE (- pow (M ∸ k)) (proj₂ (sig st w)) E)
                 (track-R† k w tr)
... | E′ , s , tr′ = E′ ,
  trans s (trans (cong (_ℕ+ cost C)
                       (size-rE (- pow (M ∸ k)) (proj₂ (sig st w)) E))
                 (ℕ.+-assoc (sizeᶠ E) 1 (cost C))) , tr′


------------------------------------------------------------------------
-- The phase of a circuit

private
  tracks-init : Tracks (init {n}) (0ℤ , [])
  tracks-init = record
    { consts = λ w → refl
    ; values = λ x y → trans (eval-0ᴾ x y) refl
    }

-- ⟦ C ⟧'s phase has a Fourier expansion with cost C ≤ 3|C| terms, at
-- the precision of the phase itself, equal to it at every point.

circuit-fourier : (C : Circuit n) →
                  ∃ λ (E : Expansion n (paths C)) →
                  sizeᶠ E ≡ cost C ×
                  (∀ x y → eval (phase ⟦ C ⟧) x y ≡ valueᶠ E x y) ×
                  FourierOf 0 E (phase ⟦ C ⟧)
circuit-fourier {n} C with track-run C (init {n}) (0ℤ , []) tracks-init
... | E , s , tr = E , s , values tr , λ x y → subst (pow (M ℕ+ 0) ∣_)
  (sym (trans (cong (λ v → valueᶠ E x y - pow 0 * v) (values tr x y))
              (zero-diff (valueᶠ E x y))))
  i∣0
  where
  zero-diff : ∀ v → v - pow 0 * v ≡ 0ℤ
  zero-diff = solve 1 (λ v → v :- con 1ℤ :* v := con 0ℤ) refl

-- At most 3|C| terms.

circuit-fourier-linear : (C : Circuit n) →
  ∃ λ (E : Expansion n (paths C)) →
  sizeᶠ E ≤ 3 ℕ* length C × FourierOf 0 E (phase ⟦ C ⟧)
circuit-fourier-linear C with circuit-fourier C
... | E , s , _ , f = E , ℕ.≤-trans (ℕ.≤-reflexive s) (cost≤ C) , f
