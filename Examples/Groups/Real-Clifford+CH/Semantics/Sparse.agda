------------------------------------------------------------------------
-- Presentations of groups
--
-- The product of stored matrices, skipping zero entries
--
-- `mulM M N` tabulates every entry of the product as a sum over all of
-- its terms, reading each factor's entry by a lookup in its trie.  The
-- matrices of these circuits are sparse — a signed permutation with a
-- few two-by-two Hadamard blocks — so `mulS` builds each row of the
-- product instead as the combination of N's rows that M's row gives,
-- skipping a row whose coefficient is zero.  It is the same trie
-- (`mulS-ok`), and it is what an evaluation that multiplies stored
-- matrices (ProdEval, CommEval) should use.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Semantics.Sparse where

open import Data.Bool using (Bool ; true ; false)
open import Data.Integer using (+_ ; -[1+_])
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁₊)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Rows

-- Is a (stored, hence literal) entry zero?
isZero : 𝔽 → Bool
isZero (+ zero +√2 + zero) = true
isZero _                   = false

scaleR : (k : ℕ) → 𝔽 → Tab k 𝔽 → Tab k 𝔽
scaleR ₀      a x       = strict (a * x)
scaleR (₁₊ k) a (l , r) = scaleR k a l , scaleR k a r

addR : (k : ℕ) → Tab k 𝔽 → Tab k 𝔽 → Tab k 𝔽
addR ₀      x       y         = strict (x + y)
addR (₁₊ k) (l , r) (l′ , r′) = addR k l l′ , addR k r r′

-- A row, or nothing for the zero row.
addMb : (k : ℕ) → Maybe (Tab k 𝔽) → Maybe (Tab k 𝔽) → Maybe (Tab k 𝔽)
addMb k nothing  q        = q
addMb k (just p) nothing  = just p
addMb k (just p) (just q) = just (addR k p q)

-- One term: the row scaled by its coefficient, or nothing.
term : (k : ℕ) → Bool → 𝔽 → Tab k 𝔽 → Maybe (Tab k 𝔽)
term k true  a row = nothing
term k false a row = just (scaleR k a row)

-- The combination of N's rows with the coefficients of one row of M.
comb : (j k : ℕ) → Tab j 𝔽 → Tab j (Tab k 𝔽) → Maybe (Tab k 𝔽)
comb ₀      k a         row       = term k (isZero a) a row
comb (₁₊ j) k (rl , rr) (nl , nr) = addMb k (comb j k rl nl) (comb j k rr nr)

rowOf : (k : ℕ) → Maybe (Tab k 𝔽) → Tab k 𝔽
rowOf k nothing  = tab k (λ _ → 0#)
rowOf k (just r) = r

mapT : (j : ℕ) {A B : Set} → (A → B) → Tab j A → Tab j B
mapT ₀      f x       = f x
mapT (₁₊ j) f (l , r) = mapT j f l , mapT j f r

-- The product.
mulS : Mat k → Mat k → Mat k
mulS {k} M N = mat (mapT k (λ row → rowOf k (comb k k row (entries N))) (entries M))

------------------------------------------------------------------------
-- It is mulM

private
  valMb : (k : ℕ) → Maybe (Tab k 𝔽) → Bits k → 𝔽
  valMb k nothing  y = 0#
  valMb k (just r) y = get r y

  get-scaleR : (k : ℕ) (a : 𝔽) (r : Tab k 𝔽) (y : Bits k) →
               get (scaleR k a r) y ≡ a * get r y
  get-scaleR ₀      a x       []           = strict-id (a * x)
  get-scaleR (₁₊ k) a (l , r) (false ∷ ys) = get-scaleR k a l ys
  get-scaleR (₁₊ k) a (l , r) (true  ∷ ys) = get-scaleR k a r ys

  get-addR : (k : ℕ) (p q : Tab k 𝔽) (y : Bits k) →
             get (addR k p q) y ≡ get p y + get q y
  get-addR ₀      x       y         []           = strict-id (x + y)
  get-addR (₁₊ k) (l , r) (l′ , r′) (false ∷ ys) = get-addR k l l′ ys
  get-addR (₁₊ k) (l , r) (l′ , r′) (true  ∷ ys) = get-addR k r r′ ys

  val-addMb : (k : ℕ) (p q : Maybe (Tab k 𝔽)) (y : Bits k) →
              valMb k (addMb k p q) y ≡ valMb k p y + valMb k q y
  val-addMb k nothing  q        y = Eq.sym (+-identityˡ (valMb k q y))
  val-addMb k (just p) nothing  y = Eq.sym (+-identityʳ (get p y))
  val-addMb k (just p) (just q) y = get-addR k p q y

  val-term : (k : ℕ) (a : 𝔽) (row : Tab k 𝔽) (y : Bits k) →
             valMb k (term k (isZero a) a row) y ≡ a * get row y
  val-term k (+ zero    +√2 + zero)    row y = Eq.sym (*-zeroˡ (get row y))
  val-term k (+ zero    +√2 + suc n)   row y = get-scaleR k _ row y
  val-term k (+ zero    +√2 -[1+ n ])  row y = get-scaleR k _ row y
  val-term k (+ suc m   +√2 b)         row y = get-scaleR k _ row y
  val-term k (-[1+ m ]  +√2 b)         row y = get-scaleR k _ row y

  -- A combination of rows is the sum the product's entry is.
  val-comb : (j k : ℕ) (r : Tab j 𝔽) (n : Tab j (Tab k 𝔽)) (y : Bits k) →
             valMb k (comb j k r n) y ≡ Σb {j} (λ z → get r z * get (get n z) y)
  val-comb ₀      k a         row       y = val-term k a row y
  val-comb (₁₊ j) k (rl , rr) (nl , nr) y =
    Eq.trans (val-addMb k (comb j k rl nl) (comb j k rr nr) y)
             (Eq.cong₂ _+_ (val-comb j k rl nl y) (val-comb j k rr nr y))

  get-rowOf : (k : ℕ) (m : Maybe (Tab k 𝔽)) (y : Bits k) →
              get (rowOf k m) y ≡ valMb k m y
  get-rowOf k nothing  y = get-tab k (λ _ → 0#) y
  get-rowOf k (just r) y = Eq.refl

  get-mapT : (j : ℕ) {A B : Set} (f : A → B) (t : Tab j A) (x : Bits j) →
             get (mapT j f t) x ≡ f (get t x)
  get-mapT ₀      f t       []           = Eq.refl
  get-mapT (₁₊ j) f (l , r) (false ∷ xs) = get-mapT j f l xs
  get-mapT (₁₊ j) f (l , r) (true  ∷ xs) = get-mapT j f r xs

mulS-ok : (M N : Mat k) → mulS M N ≡ mulM M N
mulS-ok {k} M N = mat-ext λ x y →
  Eq.trans (Eq.cong (λ t → get t y)
                    (get-mapT k (λ row → rowOf k (comb k k row (entries N))) (entries M) x))
  (Eq.trans (get-rowOf k (comb k k (get (entries M) x) (entries N)) y)
  (Eq.trans (val-comb k k (get (entries M) x) (entries N) y)
            (Eq.sym (ix-mul M N x y))))
