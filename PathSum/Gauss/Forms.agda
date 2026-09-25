------------------------------------------------------------------------
-- Presentations of groups
--
-- Linear forms at one path variable: removing it, eliminating it, and
-- reading a form that has no path variables left
--
-- The Gaussian elimination of PathSum.Gauss works on the Z₂-linear
-- forms c ⊕ ⨁_{u ∈ S} u of PathSum.Linear, one path variable y_j at a
-- time.  This module holds what that needs of the forms themselves,
-- none of which mentions a phase polynomial, the denotation, or M.
--
--  * The coefficient of y_j in a form (coefʸ), and the form with y_j
--    taken out of its set (dropᴸ j, through Vec.removeAt).  Reading a
--    form at the assignment insertᵃ j b g of PathSum.Reorder -- g on
--    the other variables, b on y_j -- adds b exactly when y_j occurs
--    (valᴸ-insertᵃ); so a form free of y_j reads the same at either
--    value of y_j, and reads there what dropᴸ j reads at g
--    (valᴸ-drop).
--
--  * Eliminating y_j by a form e in which it occurs: elimᴸ j e f adds
--    e to f exactly when y_j occurs in f, so the result is free of y_j
--    (coefʸ-elimᴸ); and wherever e reads 0 it reads what f reads
--    (valᴸ-elimᴸ).  This is one row operation of Gaussian elimination
--    over Z₂, with pivot y_j.
--
--  * Choosing the pivot: some form contains a path variable, or none
--    does (pivot?).  Whether a form has no path variable is also a
--    Boolean (pathfree): the pivot's wire becomes path-free
--    (pathfree-pivot) and a path-free wire stays so (elimᴸ-off,
--    pathfree-drop), and countᵂ counts such wires, for the bound on
--    the number of steps in PathSum.Gauss.
--
--  * A form without path variables is a form in the inputs alone, and
--    either it is x_w -- it reads the input's value on wire w at every
--    input -- or there is an input at which it reads the opposite
--    value (verdict).  The input is exhibited: the all-zero input when
--    the constant of f ⊕ x_w is 1, otherwise the unit vector of a
--    variable of f ⊕ x_w (point).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Gauss.Forms where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ; xor-same)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Subset using (Subset; inside; outside; ⁅_⁆)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_,_; ∃; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using ([]; _∷_; lookup; removeAt; zipWith)
open import Data.Vec.Properties using (lookup-zipWith; lookup-replicate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import PathSum.Assign using (_[_≔_])
open import PathSum.Linear using
  (Lin; valᴸ; varᴸ; _⊕ᴸ_; par; par-⊕; par-⁅⁆; valᴸ-⊕)
open import PathSum.Polynomial using (x[_]; y[_])
open import PathSum.Reorder using (insertᵃ; insertᵃ-here)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- Booleans

private
  xor-left-comm : ∀ a b c → a xor (b xor c) ≡ b xor (a xor c)
  xor-left-comm false b     c = refl
  xor-left-comm true  false c = refl
  xor-left-comm true  true  c = refl

  xor-cancel : ∀ a b → (a xor b) xor b ≡ a
  xor-cancel false false = refl
  xor-cancel false true  = refl
  xor-cancel true  false = refl
  xor-cancel true  true  = refl

-- Solving a xor b ≡ v for a.

xor-solve : ∀ a b v → a xor b ≡ v → a ≡ v xor b
xor-solve a b _ refl = sym (xor-cancel a b)

-- A bit is never its own negation.

not-≢ : ∀ b → not b ≢ b
not-≢ false ()
not-≢ true  ()


------------------------------------------------------------------------
-- The coefficient of a path variable, and removing it

-- Whether y_j occurs in a form.

coefʸ : Lin n m → Fin m → Bool
coefʸ (_ , _ , β) j = lookup β j

-- The form with y_j taken out of its set, over the other path
-- variables in their original order.

dropᴸ : Fin (suc m) → Lin n (suc m) → Lin n m
dropᴸ j (c , α , β) = c , α , removeAt β j

-- A parity read at insertᵃ j b g collects b exactly when j is in the
-- set, and otherwise what the set without j reads at g.

par-insertᵃ : (β : Subset (suc m)) (j : Fin (suc m)) (b : Bool)
              (g : Fin m → Bool) →
              par β (insertᵃ j b g) ≡ (lookup β j ∧ b) xor par (removeAt β j) g
par-insertᵃ         (inside  ∷ β) zero b g = refl
par-insertᵃ         (outside ∷ β) zero b g = refl
par-insertᵃ {zero}  (_ ∷ β) (suc ()) b g
par-insertᵃ {suc m} (inside  ∷ β@(_ ∷ _)) (suc j) b g = trans
  (cong (g zero xor_) (par-insertᵃ β j b (λ l → g (suc l))))
  (xor-left-comm (g zero) (lookup β j ∧ b)
                 (par (removeAt β j) (λ l → g (suc l))))
par-insertᵃ {suc m} (outside ∷ β@(_ ∷ _)) (suc j) b g =
  par-insertᵃ β j b (λ l → g (suc l))

valᴸ-insertᵃ : (l : Lin n (suc m)) (j : Fin (suc m)) (b : Bool)
               (x : Fin n → Bool) (g : Fin m → Bool) →
               valᴸ l x (insertᵃ j b g) ≡
               (coefʸ l j ∧ b) xor valᴸ (dropᴸ j l) x g
valᴸ-insertᵃ (c , α , β) j b x g = trans
  (cong (λ v → c xor (par α x xor v)) (par-insertᵃ β j b g))
  (trans (cong (c xor_) (xor-left-comm (par α x) (lookup β j ∧ b)
                                       (par (removeAt β j) g)))
         (xor-left-comm c (lookup β j ∧ b)
                        (par α x xor par (removeAt β j) g)))

-- A form free of y_j reads, at either value of y_j, what the form
-- without y_j reads.

valᴸ-drop : (l : Lin n (suc m)) (j : Fin (suc m)) (b : Bool)
            (x : Fin n → Bool) (g : Fin m → Bool) → coefʸ l j ≡ false →
            valᴸ l x (insertᵃ j b g) ≡ valᴸ (dropᴸ j l) x g
valᴸ-drop l j b x g cf = trans (valᴸ-insertᵃ l j b x g)
  (cong (λ a → (a ∧ b) xor valᴸ (dropᴸ j l) x g) cf)


------------------------------------------------------------------------
-- Coefficients of sums and of variables

coefʸ-⊕ : (l l′ : Lin n m) (j : Fin m) →
          coefʸ (l ⊕ᴸ l′) j ≡ coefʸ l j xor coefʸ l′ j
coefʸ-⊕ (c , α , β) (c′ , α′ , β′) j = lookup-zipWith _xor_ j β β′

coefʸ-x : (i : Fin n) (j : Fin m) → coefʸ (varᴸ {n} {m} x[ i ]) j ≡ false
coefʸ-x i j = lookup-replicate j outside

private
  lookup-⁅⁆ : (j : Fin k) → lookup ⁅ j ⁆ j ≡ inside
  lookup-⁅⁆ zero    = refl
  lookup-⁅⁆ (suc j) = lookup-⁅⁆ j

coefʸ-y : (j : Fin m) → coefʸ (varᴸ {n} {m} y[ j ]) j ≡ true
coefʸ-y j = lookup-⁅⁆ j


------------------------------------------------------------------------
-- Eliminating a path variable from a form

-- Adding e wherever y_j occurs.  When y_j occurs in e this clears it,
-- and where e reads 0 nothing is changed.

elimᴸ : Fin m → Lin n m → Lin n m → Lin n m
elimᴸ j e f = if coefʸ f j then f ⊕ᴸ e else f

coefʸ-elimᴸ : (j : Fin m) (e f : Lin n m) → coefʸ e j ≡ true →
              coefʸ (elimᴸ j e f) j ≡ false
coefʸ-elimᴸ j e f ce = go (coefʸ f j) refl
  where
  go : ∀ b → coefʸ f j ≡ b → coefʸ (if b then f ⊕ᴸ e else f) j ≡ false
  go true  cf = trans (coefʸ-⊕ f e j) (cong₂ _xor_ cf ce)
  go false cf = cf

valᴸ-elimᴸ : (j : Fin m) (e f : Lin n m) (x : Fin n → Bool)
             (y : Fin m → Bool) → valᴸ e x y ≡ false →
             valᴸ (elimᴸ j e f) x y ≡ valᴸ f x y
valᴸ-elimᴸ j e f x y ve = go (coefʸ f j)
  where
  go : ∀ b → valᴸ (if b then f ⊕ᴸ e else f) x y ≡ valᴸ f x y
  go true  = trans (valᴸ-⊕ f e x y)
    (trans (cong (valᴸ f x y xor_) ve) (xor-identityʳ (valᴸ f x y)))
  go false = refl


-- The elimination of y_j leaves a form free of y_j alone, and adds e
-- to one containing it.

elimᴸ-off : (j : Fin m) (e f : Lin n m) → coefʸ f j ≡ false →
            elimᴸ j e f ≡ f
elimᴸ-off j e f cf = cong (λ b → if b then f ⊕ᴸ e else f) cf

elimᴸ-on : (j : Fin m) (e f : Lin n m) → coefʸ f j ≡ true →
           elimᴸ j e f ≡ f ⊕ᴸ e
elimᴸ-on j e f cf = cong (λ b → if b then f ⊕ᴸ e else f) cf


------------------------------------------------------------------------
-- Forms without path variables, as a Boolean

-- The coefficients left after removing y_j are the others, in order.

private
  lookup-removeAt : (β : Subset (suc m)) (j : Fin (suc m)) (i : Fin m) →
                    lookup (removeAt β j) i ≡ lookup β (punchIn j i)
  lookup-removeAt         (b ∷ β)         zero    i       = refl
  lookup-removeAt {zero}  (b ∷ β)         (suc ()) i
  lookup-removeAt {suc m} (b ∷ β@(_ ∷ _)) (suc j) zero    = refl
  lookup-removeAt {suc m} (b ∷ β@(_ ∷ _)) (suc j) (suc i) =
    lookup-removeAt β j i

coefʸ-drop : (l : Lin n (suc m)) (j : Fin (suc m)) (i : Fin m) →
             coefʸ (dropᴸ j l) i ≡ coefʸ l (punchIn j i)
coefʸ-drop (c , α , β) j i = lookup-removeAt β j i

-- Whether a set is empty, and whether a form has no path variable.

noneᵇ : Subset k → Bool
noneᵇ []            = true
noneᵇ (inside  ∷ p) = false
noneᵇ (outside ∷ p) = noneᵇ p

noneᵇ-true : (p : Subset k) → noneᵇ p ≡ true → ∀ i → lookup p i ≡ false
noneᵇ-true (inside  ∷ p) ()
noneᵇ-true (outside ∷ p) e zero    = refl
noneᵇ-true (outside ∷ p) e (suc i) = noneᵇ-true p e i

noneᵇ-intro : (p : Subset k) → (∀ i → lookup p i ≡ false) → noneᵇ p ≡ true
noneᵇ-intro []            h = refl
noneᵇ-intro (inside  ∷ p) h = contradiction (h zero) λ ()
noneᵇ-intro (outside ∷ p) h = noneᵇ-intro p (λ i → h (suc i))

pathfree : Lin n m → Bool
pathfree (_ , _ , β) = noneᵇ β

pathfree-true : (l : Lin n m) → pathfree l ≡ true →
                ∀ i → coefʸ l i ≡ false
pathfree-true (c , α , β) = noneᵇ-true β

pathfree-intro : (l : Lin n m) → (∀ i → coefʸ l i ≡ false) →
                 pathfree l ≡ true
pathfree-intro (c , α , β) = noneᵇ-intro β

-- Removing y_j keeps a form free of path variables.

pathfree-drop : (j : Fin (suc m)) (l : Lin n (suc m)) → pathfree l ≡ true →
                pathfree (dropᴸ j l) ≡ true
pathfree-drop j l pf = pathfree-intro (dropᴸ j l) (λ i →
  trans (coefʸ-drop l j i) (pathfree-true l pf (punchIn j i)))

-- Eliminating y_j from f by a form with the same path-variable
-- coefficients clears every path variable of f: that is what happens
-- to the pivot's own wire.

pathfree-pivot : (j : Fin (suc m)) (e f : Lin n (suc m)) →
                 coefʸ f j ≡ true → (∀ i → coefʸ e i ≡ coefʸ f i) →
                 pathfree (dropᴸ j (elimᴸ j e f)) ≡ true
pathfree-pivot j e f cf same =
  trans (cong (λ l → pathfree (dropᴸ j l)) (elimᴸ-on j e f cf))
    (pathfree-intro (dropᴸ j (f ⊕ᴸ e)) (λ i →
      trans (coefʸ-drop (f ⊕ᴸ e) j i)
        (trans (coefʸ-⊕ f e (punchIn j i))
          (trans (cong (coefʸ f (punchIn j i) xor_) (same (punchIn j i)))
                 (xor-same (coefʸ f (punchIn j i)))))))


------------------------------------------------------------------------
-- Counting wires

-- The number of wires with a property.

private
  bitⁿ : Bool → ℕ
  bitⁿ true  = 1
  bitⁿ false = 0

  bitⁿ-≤ : ∀ b → bitⁿ b ≤ 1
  bitⁿ-≤ true  = ℕ.≤-refl
  bitⁿ-≤ false = z≤n

  bitⁿ-mono : ∀ a b → (a ≡ true → b ≡ true) → bitⁿ a ≤ bitⁿ b
  bitⁿ-mono false b h = z≤n
  bitⁿ-mono true  b h = ℕ.≤-reflexive (cong bitⁿ (sym (h refl)))

countᵂ : (Fin n → Bool) → ℕ
countᵂ {zero}  p = 0
countᵂ {suc n} p = bitⁿ (p zero) + countᵂ (λ w → p (suc w))

countᵂ-≤ : (p : Fin n → Bool) → countᵂ p ≤ n
countᵂ-≤ {zero}  p = z≤n
countᵂ-≤ {suc n} p =
  ℕ.+-mono-≤ (bitⁿ-≤ (p zero)) (countᵂ-≤ (λ w → p (suc w)))

countᵂ-mono : (p q : Fin n → Bool) → (∀ w → p w ≡ true → q w ≡ true) →
              countᵂ p ≤ countᵂ q
countᵂ-mono {zero}  p q h = z≤n
countᵂ-mono {suc n} p q h = ℕ.+-mono-≤ (bitⁿ-mono (p zero) (q zero) (h zero))
  (countᵂ-mono (λ w → p (suc w)) (λ w → q (suc w)) (λ w → h (suc w)))

-- One more wire with the property, and none fewer: the count grows.

countᵂ-grow : (p q : Fin n → Bool) → (∀ w → p w ≡ true → q w ≡ true) →
              (w : Fin n) → p w ≡ false → q w ≡ true →
              suc (countᵂ p) ≤ countᵂ q
countᵂ-grow {zero}  p q h () pw qw
countᵂ-grow {suc n} p q h zero pw qw rewrite pw | qw =
  s≤s (countᵂ-mono (λ w → p (suc w)) (λ w → q (suc w)) (λ w → h (suc w)))
countᵂ-grow {suc n} p q h (suc w) pw qw = ℕ.≤-trans
  (ℕ.≤-reflexive (sym (ℕ.+-suc (bitⁿ (p zero)) (countᵂ (λ v → p (suc v))))))
  (ℕ.+-mono-≤ (bitⁿ-mono (p zero) (q zero) (h zero))
    (countᵂ-grow (λ v → p (suc v)) (λ v → q (suc v)) (λ v → h (suc v))
                 w pw qw))


------------------------------------------------------------------------
-- Assignments with one path variable inserted

-- The positions other than j do not see the value inserted at j.

insertᵃ-other : (j : Fin (suc m)) (a b : Bool) (g : Fin m → Bool)
                (i : Fin (suc m)) → i ≢ j →
                insertᵃ j a g i ≡ insertᵃ j b g i
insertᵃ-other         zero    a b g zero    ne = contradiction refl ne
insertᵃ-other         zero    a b g (suc i) ne = refl
insertᵃ-other {zero}  (suc ()) a b g i ne
insertᵃ-other {suc m} (suc j) a b g zero    ne = refl
insertᵃ-other {suc m} (suc j) a b g (suc i) ne =
  insertᵃ-other j a b (λ l → g (suc l)) i (λ eq → ne (cong suc eq))

-- Overwriting the inserted value is inserting the new one.

≔-insertᵃ : (j : Fin (suc m)) (a b : Bool) (g : Fin m → Bool) →
            ∀ i → ((insertᵃ j a g) [ j ≔ b ]) i ≡ insertᵃ j b g i
≔-insertᵃ j a b g i with i Fin.≟ j
... | yes refl = sym (insertᵃ-here j b g)
... | no  i≢j  = insertᵃ-other j a b g i i≢j


------------------------------------------------------------------------
-- Searching finitely many wires

-- Either one of the wires has the first property, or all of them have
-- the second.

some-or-all : {A B : Fin n → Set} → (∀ w → A w ⊎ B w) →
              (∃ A) ⊎ (∀ w → B w)
some-or-all {zero}          d = inj₂ λ ()
some-or-all {suc n} {A} {B} d = first (d zero)
  where
  rest : (∃ λ w → A (suc w)) ⊎ (∀ w → B (suc w))
  rest = some-or-all {A = λ w → A (suc w)} {B = λ w → B (suc w)}
                     (λ w → d (suc w))

  later : B zero → (∃ λ w → A (suc w)) ⊎ (∀ w → B (suc w)) →
          (∃ A) ⊎ (∀ w → B w)
  later b (inj₁ (w , a)) = inj₁ (suc w , a)
  later b (inj₂ bs)      = inj₂ λ { zero → b ; (suc w) → bs w }

  first : A zero ⊎ B zero → (∃ A) ⊎ (∀ w → B w)
  first (inj₁ a) = inj₁ (zero , a)
  first (inj₂ b) = later b rest

-- A set either has an element or has none.

find : (p : Subset k) → (∃ λ i → lookup p i ≡ true) ⊎ (∀ i → lookup p i ≡ false)
find []            = inj₂ λ ()
find (inside  ∷ p) = inj₁ (zero , refl)
find (outside ∷ p) = later (find p)
  where
  later : (∃ λ i → lookup p i ≡ true) ⊎ (∀ i → lookup p i ≡ false) →
          (∃ λ i → lookup (outside ∷ p) i ≡ true) ⊎
          (∀ i → lookup (outside ∷ p) i ≡ false)
  later (inj₁ (i , e)) = inj₁ (suc i , e)
  later (inj₂ h)       = inj₂ λ { zero → refl ; (suc i) → h i }


------------------------------------------------------------------------
-- Choosing the pivot

-- The next step of the elimination: a wire whose form contains some
-- path variable, or the knowledge that no form contains one.

data Pivot {n m : ℕ} (σ : Fin n → Lin n m) : Set where
  pivot : (w : Fin n) (j : Fin m) → coefʸ (σ w) j ≡ true → Pivot σ
  none  : (∀ w j → coefʸ (σ w) j ≡ false) → Pivot σ

pivot? : (σ : Fin n → Lin n m) → Pivot σ
pivot? σ = by (some-or-all (λ w → find (proj₂ (proj₂ (σ w)))))
  where
  by : (∃ λ w → ∃ λ j → coefʸ (σ w) j ≡ true) ⊎
       (∀ w j → coefʸ (σ w) j ≡ false) → Pivot σ
  by (inj₁ (w , j , e)) = pivot w j e
  by (inj₂ h)           = none h


------------------------------------------------------------------------
-- Forms without path variables

-- The unit vector at i.

point : Fin k → Fin k → Bool
point zero    zero    = true
point zero    (suc _) = false
point (suc i) zero    = false
point (suc i) (suc l) = point i l

par-const-false : (p : Subset k) → par p (λ _ → false) ≡ false
par-const-false []            = refl
par-const-false (inside  ∷ p) = par-const-false p
par-const-false (outside ∷ p) = par-const-false p

par-point : (p : Subset k) (i : Fin k) → par p (point i) ≡ lookup p i
par-point (inside  ∷ p) zero    = cong (true xor_) (par-const-false p)
par-point (outside ∷ p) zero    = par-const-false p
par-point (inside  ∷ p) (suc i) = par-point p i
par-point (outside ∷ p) (suc i) = par-point p i

par-none : (p : Subset k) (f : Fin k → Bool) →
           (∀ i → lookup p i ≡ false) → par p f ≡ false
par-none []            f h = refl
par-none (inside  ∷ p) f h = contradiction (h zero) λ ()
par-none (outside ∷ p) f h =
  par-none p (λ i → f (suc i)) (λ i → h (suc i))

-- A form without path variables either reads x_w everywhere, or at
-- some input reads the opposite of x_w on every path.  Writing the
-- form as c ⊕ ⨁α, compare α with {w}: their sum α′ = α ⊕ {w} reads
-- f ⊕ x_w apart from c.  If c = 1 the zero input refutes; if α′ has
-- an element i the unit vector at i refutes; otherwise f is x_w.

verdict : (f : Lin n m) (w : Fin n) → (∀ j → coefʸ f j ≡ false) →
          (∃ λ x → ∀ y → valᴸ f x y ≡ not (x w)) ⊎
          (∀ x y → valᴸ f x y ≡ x w)
verdict (c , α , β) w free = by-const c
  where
  α′ : Subset _
  α′ = zipWith _xor_ α ⁅ w ⁆

  noy : ∀ y → par β y ≡ false
  noy y = par-none β y free

  -- The value, the constant apart, is that of α; and α′ reads it
  -- together with x_w.

  α′-reads : ∀ x → par α x xor x w ≡ par α′ x
  α′-reads x = sym (trans (par-⊕ α ⁅ w ⁆ x) (cong (par α x xor_) (par-⁅⁆ w x)))

  body : ∀ x y → par α x xor par β y ≡ par α x
  body x y = trans (cong (par α x xor_) (noy y)) (xor-identityʳ (par α x))

  by-set : (∃ λ i → lookup α′ i ≡ true) ⊎ (∀ i → lookup α′ i ≡ false) →
           (∃ λ x → ∀ y → valᴸ (false , α , β) x y ≡ not (x w)) ⊎
           (∀ x y → valᴸ (false , α , β) x y ≡ x w)
  by-set (inj₁ (i , e)) = inj₁ (point i , λ y → trans (body (point i) y)
    (xor-solve (par α (point i)) (point i w) true
      (trans (α′-reads (point i)) (trans (par-point α′ i) e))))
  by-set (inj₂ h) = inj₂ λ x y → trans (body x y)
    (xor-solve (par α x) (x w) false
      (trans (α′-reads x) (par-none α′ x h)))

  by-const : ∀ c → (∃ λ x → ∀ y → valᴸ (c , α , β) x y ≡ not (x w)) ⊎
                   (∀ x y → valᴸ (c , α , β) x y ≡ x w)
  by-const true  = inj₁ ((λ _ → false) , λ y →
    cong not (trans (body (λ _ → false) y) (par-const-false α)))
  by-const false = by-set (find α′)
