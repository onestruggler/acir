------------------------------------------------------------------------
-- Presentations of groups
--
-- The normal form of Clément's Lemma A.4
--
-- Appendix A.4 proves Theorem 4.10 not by writing derivations out but
-- by a normal form: any word over P with no Hadamard letter is
-- equivalent to a unique word
--
--     ((−1)[a₁](−1)[b₁]) ⋯ ((−1)[a_k](−1)[b_k])
--       ∏_{i=1}^{N−1} ( ∏_{j=dᵢ}^{N−i−1} ((−1)[j] X[j,j+1]) )
--
-- with a₁ < b₁ < ⋯ < a_k < b_k and dᵢ ∈ {0,…,N−i}, both products in
-- increasing order and an empty one being ε.  Corollary A.5 then reads
-- off that two such words with the same semantics are equal, which is
-- what discharges the Reidemeister–Schreier obligations that carry no
-- Hadamard letter.
--
-- The two halves are a subset and a permutation.  The sign part is an
-- even-sized subset of the indices, written as its elements paired off
-- in increasing order, so it ranges over 2^(N−1) values; it is kept
-- here as the sorted list of those elements, since that is what a
-- product of sign letters actually determines.  The permutation part
-- is a Lehmer code: the vector (d₁,…,d_{N−1}) ranges over
-- ∏(N−i+1) = N! values, each giving a product of letters on
-- *consecutive* pairs only.  That the two together are a normal form
-- was checked by enumeration before any of this was written
-- (`scratchpad/tNF.py`): at N = 2, 3, 4, 5 the words number exactly
-- 2^(N−1)·N! and no two have the same matrix.
--
-- The permutation part is indexed by natural numbers, through
-- `Encoding`'s deciding wrapper `zxℕ`, because its indices are
-- literals and `Fin N` has none at a symbolic width.  The sign part
-- needs no wrapper: its indices come from the word being normalised,
-- and `zz` is total.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.NF (m : ℕ) where

open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Bool using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Properties using (_≟_ ; toℕ-injective ; toℕ-fromℕ< ; toℕ<n)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Nat using (zero ; suc ; _+_ ; _<_ ; _≤_ ; _∸_ ; _<?_ ; z≤n ; s≤s)
  renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; subst₂)
open import Relation.Nullary using (Dec ; yes ; no)
open import Data.Nat.Properties
  using (≤-<-trans ; <-trans ; ≤-trans ; <-≤-trans ; ≤-refl ; ≤-reflexive
       ; <⇒≤ ; ≮⇒≥ ; ≤∧≢⇒< ; n<1+n ; n≤1+n ; n≮n ; <-cmp
       ; suc-injective ; +-suc ; +-identityʳ ; +-monoʳ-< ; m≤n+m ; m∸n+n≡m
       ; m+[n∸m]≡n ; ∸-monoʳ-≤ ; n∸n≡0 ; <-irrefl ; ≤-antisym)
  renaming (_≟_ to _≟ⁿ_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (parity)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m
  using (zz-comm ; zz-split ; zz² ; DE-ZZ ; zx²′ ; disj-int ; zxℕ-zx ; zzℕ-zz
       ; Conj ; conj-any ; flip′
       ; next ; next-Succ ; prev ; prev-toℕ ; prev-Succ ; ∸suc ; pred∸
       ; pred≤pred ; 0<∸)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
  using (GenP ; −1−1 ; −1X ; XX)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (o₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (_≐_ ; sp ; sound ; ≐-sym ; ≐-trans)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx ; xx ; zxℕ ; zzℕ)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m PF,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- The permutation part

-- A run of letters on consecutive pairs: k of them, from d upwards.
runFrom : ℕ → ℕ → W
runFrom d zero    = ε
runFrom d (suc k) = zxℕ d d (suc d) • runFrom (suc d) k

-- The i-th run: the pairs (j , j + 1) for j from dᵢ to N − i − 1.
runAt : ℕ → ℕ → W
runAt i dᵢ = runFrom dᵢ (N ∸ i ∸ dᵢ)

-- k runs, from the i-th on.
permFrom : ℕ → ℕ → (ℕ → ℕ) → W
permFrom i zero    d = ε
permFrom i (suc k) d = runAt i (d i) • permFrom (suc i) k d

-- The runs for i = 1 … N − 1.
permPart : (ℕ → ℕ) → W
permPart = permFrom 1 (N ∸ 1)

-- A Lehmer code: dᵢ ≤ N − i.  (Outside 1 … N − 1 the value is unused.)
Lehmer : (ℕ → ℕ) → Set
Lehmer d = ∀ i → d i ≤ N ∸ i

------------------------------------------------------------------------
-- The sign part
--
-- The sorted list of indices carrying a sign, paired off two at a
-- time.  An odd list cannot occur under the side condition below, and
-- the last element is dropped if one does.

signOf : List (Fin N) → W
signOf []           = ε
signOf (a ∷ [])     = ε
signOf (a ∷ b ∷ l)  = zz a b • signOf l

-- Strictly increasing, which makes the list the subset it denotes.
data Incr : ℕ → List (Fin N) → Set where
  nil  : ∀ {lo} → Incr lo []
  cons : ∀ {lo a l} → lo < toℕ a → Incr (toℕ a) l → Incr lo (a ∷ l)

-- Even length, so that no element is dropped.  Stated with its
-- companion, since a single toggle flips the parity.
mutual
  data Even : List (Fin N) → Set where
    nil  : Even []
    cons : ∀ {a l} → Odd l → Even (a ∷ l)

  data Odd : List (Fin N) → Set where
    cons : ∀ {a l} → Even l → Odd (a ∷ l)

-- The same with no bound on the first element: (B) allows a sign on
-- the index 0, so the sign part is any increasing list, not one that
-- starts above 0.
data Incr₀ : List (Fin N) → Set where
  nil  : Incr₀ []
  cons : ∀ {a l} → Incr (toℕ a) l → Incr₀ (a ∷ l)

Incr⇒Incr₀ : ∀ {lo l} → Incr lo l → Incr₀ l
Incr⇒Incr₀ nil        = nil
Incr⇒Incr₀ (cons _ i) = cons i

-- Lowering the bound on an increasing list.
Incr-mono : ∀ {lo lo′ l} → lo ≤ lo′ → Incr lo′ l → Incr lo l
Incr-mono le nil        = nil
Incr-mono le (cons lt i) = cons (≤-<-trans le lt) i

------------------------------------------------------------------------
-- The sign part is central
--
-- Sign letters commute with one another, so a sign part commutes with
-- any sign letter and with any other sign part.

signOf-zz : ∀ (l : List (Fin N)) (x y : Fin N) →
            signOf l • zz x y ≈ zz x y • signOf l
signOf-zz []          x y = trans left-unit (sym right-unit)
signOf-zz (a ∷ [])    x y = trans left-unit (sym right-unit)
signOf-zz (a ∷ b ∷ l) x y = begin
  (zz a b • signOf l) • zz x y   ≈⟨ assoc ⟩
  zz a b • (signOf l • zz x y)   ≈⟨ back _ (signOf-zz l x y) ⟩
  zz a b • (zz x y • signOf l)   ≈⟨ sym assoc ⟩
  (zz a b • zz x y) • signOf l   ≈⟨ front _ (zz-comm a b x y) ⟩
  (zz x y • zz a b) • signOf l   ≈⟨ assoc ⟩
  zz x y • (zz a b • signOf l) ∎

signOf-comm : ∀ (l l′ : List (Fin N)) →
              signOf l • signOf l′ ≈ signOf l′ • signOf l
signOf-comm l []          = trans right-unit (sym left-unit)
signOf-comm l (a ∷ [])    = trans right-unit (sym left-unit)
signOf-comm l (a ∷ b ∷ k) = begin
  signOf l • (zz a b • signOf k)   ≈⟨ sym assoc ⟩
  (signOf l • zz a b) • signOf k   ≈⟨ front _ (signOf-zz l a b) ⟩
  (zz a b • signOf l) • signOf k   ≈⟨ assoc ⟩
  zz a b • (signOf l • signOf k)   ≈⟨ back _ (signOf-comm l k) ⟩
  zz a b • (signOf k • signOf l)   ≈⟨ sym assoc ⟩
  (zz a b • signOf k) • signOf l ∎

------------------------------------------------------------------------
-- The normal form

NF : List (Fin N) → (ℕ → ℕ) → W
NF l d = signOf l • permPart d

-- Its side conditions.
record Normal (l : List (Fin N)) (d : ℕ → ℕ) : Set where
  constructor normal
  field
    incr   : Incr₀ l
    even   : Even l
    lehmer : Lehmer d

------------------------------------------------------------------------
-- The sign part as a product of atoms
--
-- Pairing the indices off two at a time is the canonical spelling,
-- but it is not the convenient one: adding an index to the set shifts
-- every pair after it.  (DE-ZZ) cuts each pair through the index 1,
--
--     zz a b  ≈  zz 1 a • zz 1 b,
--
-- so a sign part is equally a product of one *atom* per index, and
-- those atoms commute and square to ε.  In that spelling adding an
-- index is a local operation, which is what the reduction needs.

atoms : List (Fin N) → W
atoms []      = ε
atoms (x ∷ l) = zz o₁ x • atoms l

-- The two spellings agree on an even list.
signOf-atoms : ∀ (l : List (Fin N)) → Even l → signOf l ≈ atoms l
signOf-atoms []          nil               = refl
signOf-atoms (a ∷ b ∷ l) (cons (cons e)) = begin
  zz a b • signOf l              ≈⟨ cong (DE-ZZ a b) (signOf-atoms l e) ⟩
  (zz o₁ a • zz o₁ b) • atoms l  ≈⟨ assoc ⟩
  zz o₁ a • (zz o₁ b • atoms l) ∎

-- An atom passes a product of atoms.
atoms-zz : ∀ (l : List (Fin N)) (x : Fin N) →
           atoms l • zz o₁ x ≈ zz o₁ x • atoms l
atoms-zz []      x = trans left-unit (sym right-unit)
atoms-zz (y ∷ l) x = begin
  (zz o₁ y • atoms l) • zz o₁ x   ≈⟨ assoc ⟩
  zz o₁ y • (atoms l • zz o₁ x)   ≈⟨ back _ (atoms-zz l x) ⟩
  zz o₁ y • (zz o₁ x • atoms l)   ≈⟨ sym assoc ⟩
  (zz o₁ y • zz o₁ x) • atoms l   ≈⟨ front _ (zz-comm o₁ y o₁ x) ⟩
  (zz o₁ x • zz o₁ y) • atoms l   ≈⟨ assoc ⟩
  zz o₁ x • (zz o₁ y • atoms l) ∎

------------------------------------------------------------------------
-- Toggling an index
--
-- Sorted insertion when the index is absent, deletion when it is
-- present.  On atoms that is multiplication by one atom, since an atom
-- is an involution.

toggle : Fin N → List (Fin N) → List (Fin N)
toggle x []      = x ∷ []
toggle x (y ∷ l) with toℕ x <? toℕ y
... | yes _ = x ∷ y ∷ l
... | no  _ with x ≟ y
...         | yes _ = l
...         | no  _ = y ∷ toggle x l

atoms-toggle : ∀ (x : Fin N) (l : List (Fin N)) →
               atoms (toggle x l) ≈ zz o₁ x • atoms l
atoms-toggle x []      = refl
atoms-toggle x (y ∷ l) with toℕ x <? toℕ y
... | yes _ = refl
... | no  _ with x ≟ y
...         | yes Eq.refl = sym (cancelˡ (atoms l) (zz² o₁ x))
...         | no  _ = begin
  zz o₁ y • atoms (toggle x l)    ≈⟨ back _ (atoms-toggle x l) ⟩
  zz o₁ y • (zz o₁ x • atoms l)   ≈⟨ sym assoc ⟩
  (zz o₁ y • zz o₁ x) • atoms l   ≈⟨ front _ (zz-comm o₁ y o₁ x) ⟩
  (zz o₁ x • zz o₁ y) • atoms l   ≈⟨ assoc ⟩
  zz o₁ x • (zz o₁ y • atoms l) ∎

------------------------------------------------------------------------
-- Merging a sign letter into the sign part
--
-- Two toggles, one per index of the letter.  This is the step the
-- reduction takes whenever it meets a sign letter.

merge-zz : ∀ (x y : Fin N) (l : List (Fin N)) →
           zz x y • atoms l ≈ atoms (toggle x (toggle y l))
merge-zz x y l = begin
  zz x y • atoms l
    ≈⟨ front _ (DE-ZZ x y) ⟩
  (zz o₁ x • zz o₁ y) • atoms l
    ≈⟨ assoc ⟩
  zz o₁ x • (zz o₁ y • atoms l)
    ≈⟨ back _ (sym (atoms-toggle y l)) ⟩
  zz o₁ x • atoms (toggle y l)
    ≈⟨ sym (atoms-toggle x (toggle y l)) ⟩
  atoms (toggle x (toggle y l)) ∎

------------------------------------------------------------------------
-- Toggling keeps the side conditions
--
-- It inserts or deletes one index, so it keeps the list increasing and
-- flips its parity.  Two toggles therefore take a normal sign part to
-- a normal sign part, which is what merging a sign letter needs.

toggle-Incr : ∀ {lo} (x : Fin N) (l : List (Fin N)) →
              lo < toℕ x → Incr lo l → Incr lo (toggle x l)
toggle-Incr x []      lo<x nil = cons lo<x nil
toggle-Incr x (y ∷ l) lo<x (cons lo<y i) with toℕ x <? toℕ y
... | yes x<y = cons lo<x (cons x<y i)
... | no  x≮y with x ≟ y
...           | yes Eq.refl = Incr-mono (<⇒≤ lo<y) i
...           | no  x≢y =
  cons lo<y (toggle-Incr x l (≤∧≢⇒< (≮⇒≥ x≮y) (λ e → x≢y (toℕ-injective (Eq.sym e)))) i)

toggle-Incr₀ : ∀ (x : Fin N) (l : List (Fin N)) → Incr₀ l → Incr₀ (toggle x l)
toggle-Incr₀ x []      nil      = cons nil
toggle-Incr₀ x (y ∷ l) (cons i) with toℕ x <? toℕ y
... | yes x<y = cons (cons x<y i)
... | no  x≮y with x ≟ y
...           | yes Eq.refl = Incr⇒Incr₀ i
...           | no  x≢y =
  cons (toggle-Incr x l (≤∧≢⇒< (≮⇒≥ x≮y) (λ e → x≢y (toℕ-injective (Eq.sym e)))) i)

mutual
  toggle-Even : ∀ (x : Fin N) (l : List (Fin N)) → Even l → Odd (toggle x l)
  toggle-Even x []      nil = cons nil
  toggle-Even x (y ∷ l) (cons o) with toℕ x <? toℕ y
  ... | yes _ = cons (cons o)
  ... | no  _ with x ≟ y
  ...         | yes _ = o
  ...         | no  _ = cons (toggle-Odd x l o)

  toggle-Odd : ∀ (x : Fin N) (l : List (Fin N)) → Odd l → Even (toggle x l)
  toggle-Odd x (y ∷ l) (cons e) with toℕ x <? toℕ y
  ... | yes _ = cons (cons e)
  ... | no  _ with x ≟ y
  ...         | yes _ = e
  ...         | no  _ = cons (toggle-Even x l e)

-- Two toggles keep a sign part normal.
toggle²-Incr : ∀ (x y : Fin N) (l : List (Fin N)) →
               Incr₀ l → Incr₀ (toggle x (toggle y l))
toggle²-Incr x y l i = toggle-Incr₀ x _ (toggle-Incr₀ y l i)

toggle²-Even : ∀ (x y : Fin N) (l : List (Fin N)) →
               Even l → Even (toggle x (toggle y l))
toggle²-Even x y l e = toggle-Odd x _ (toggle-Even y l e)

------------------------------------------------------------------------
-- The normal form in the atom spelling, and the sign step
--
-- Reducing a word to normal form processes it from the right, so each
-- letter arrives on the *left* of what is already normal.  For a sign
-- letter that step is now immediate: it merges into the sign part by
-- two toggles, and the permutation part is untouched.

NFa : List (Fin N) → (ℕ → ℕ) → W
NFa l d = atoms l • permPart d

NF-atoms : ∀ (l : List (Fin N)) (d : ℕ → ℕ) → Even l → NF l d ≈ NFa l d
NF-atoms l d e = front _ (signOf-atoms l e)

-- A sign letter arriving on the left.
absorb-zz : ∀ (x y : Fin N) (l : List (Fin N)) (d : ℕ → ℕ) →
            zz x y • NFa l d ≈ NFa (toggle x (toggle y l)) d
absorb-zz x y l d = trans (sym assoc) (front _ (merge-zz x y l))

-- And it keeps the side conditions.
absorb-zz-Normal : ∀ (x y : Fin N) (l : List (Fin N)) (d : ℕ → ℕ) →
                   Normal l d → Normal (toggle x (toggle y l)) d
absorb-zz-Normal x y l d nm =
  normal (toggle²-Incr x y l (Normal.incr nm))
         (toggle²-Even x y l (Normal.even nm))
         (Normal.lehmer nm)

------------------------------------------------------------------------
-- The letters of the permutation part, and their relations
--
-- The permutation part is a word in the letters on consecutive pairs,
--
--     sx j  =  (−1)[j] X[j,j+1],
--
-- and three relations govern them: a square is a sign pair (the
-- general (23)), letters on pairs two apart commute (Figure 9's (64),
-- in the disjoint-interval case), and neighbouring letters braid
-- ((24)).  Those are exactly the relations of the signed symmetric
-- group's positive part, and (B) is its standard normal form.
--
-- The letters carry natural-number indices, since their indices are
-- literals; each relation is the Fin-indexed one of `DE` carried
-- across by `zxℕ-zx`.  The conversions are built with `cong` rather
-- than `rewrite`, which would generalise the index inside its own
-- bound.

-- An index below N.
fin : (j : ℕ) → j < N → Fin N
fin j p = fromℕ< p

fin-toℕ : ∀ (j : ℕ) (p : j < N) → toℕ (fin j p) ≡ j
fin-toℕ j p = toℕ-fromℕ< p

sx : ℕ → W
sx j = zxℕ j j (suc j)

sx-zx : ∀ (j : ℕ) (q : j < N) (p : suc j < N) →
        sx j ≡ zx (fin j q) (fin j q) (fin (suc j) p)
sx-zx j q p =
  Eq.trans (Eq.cong₂ (λ u v → zxℕ u u v)
                     (Eq.sym (fin-toℕ j q)) (Eq.sym (fin-toℕ (suc j) p)))
           (zxℕ-zx (fin j q) (fin j q) (fin (suc j) p))

zzℕ-fin : ∀ (j : ℕ) (q : j < N) (p : suc j < N) →
          zzℕ j (suc j) ≡ zz (fin j q) (fin (suc j) p)
zzℕ-fin j q p =
  Eq.trans (Eq.cong₂ zzℕ (Eq.sym (fin-toℕ j q)) (Eq.sym (fin-toℕ (suc j) p)))
           (zzℕ-zz (fin j q) (fin (suc j) p))

private
  fin≢ : ∀ {j k : ℕ} (q : j < N) (p : k < N) → j ≢ k → fin j q ≢ fin k p
  fin≢ {j} {k} q p ne e =
    ne (Eq.trans (Eq.sym (fin-toℕ j q)) (Eq.trans (Eq.cong toℕ e) (fin-toℕ k p)))

  n≢sn : ∀ (j : ℕ) → j ≢ suc j
  n≢sn (suc j) e = n≢sn j (suc-injective e)

  fin< : ∀ {j k : ℕ} (q : j < N) (p : k < N) → j < k → toℕ (fin j q) < toℕ (fin k p)
  fin< {j} {k} q p lt =
    subst₂ _<_ (Eq.sym (fin-toℕ j q)) (Eq.sym (fin-toℕ k p)) lt

  fin-succ : ∀ (j : ℕ) (q : j < N) (p : suc j < N) →
             toℕ (fin (suc j) p) ≡ suc (toℕ (fin j q))
  fin-succ j q p =
    Eq.trans (fin-toℕ (suc j) p) (Eq.cong suc (Eq.sym (fin-toℕ j q)))

-- A square is a sign pair: the general (23).
sx-square : ∀ (j : ℕ) (q : j < N) (p : suc j < N) → sx j • sx j ≈ zzℕ j (suc j)
sx-square j q p rewrite sx-zx j q p | zzℕ-fin j q p = zx²′ _ _ (fin≢ q p (n≢sn j))

-- Letters on pairs two apart commute: (64) for disjoint intervals.
sx-far : ∀ (i j : ℕ) (qi : i < N) (pi : suc i < N) (qj : j < N) (pj : suc j < N) →
         suc i < j → sx j • sx i ≈ sx i • sx j
sx-far i j qi pi qj pj lt rewrite sx-zx i qi pi | sx-zx j qj pj =
  disj-int _ _ _ _ (fin< qi pi (n<1+n i)) (fin< pi qj lt) (fin< qj pj (n<1+n j))

-- Neighbouring letters braid: (24).
sx-braid : ∀ (j : ℕ) (q : j < N) (p : suc j < N) (r : suc (suc j) < N) →
           sx j • sx (suc j) • sx j ≈ sx (suc j) • sx j • sx (suc j)
sx-braid j q p r rewrite sx-zx j q p | sx-zx (suc j) p r =
  axiom (r24 _ _ _ (fin-succ j q p) (fin-succ (suc j) p r))

------------------------------------------------------------------------
-- How a letter meets a run
--
-- Reducing a word to normal form pushes one letter at a time into the
-- permutation part, and what happens is decided by where the letter
-- sits relative to the run it meets:
--
--   * below it by two or more — it commutes straight past (`sx-below`);
--   * just below its start      — the run extends, definitionally;
--   * at its start              — the square becomes a sign, (23);
--   * inside it                 — it passes through and comes out one
--                                 lower, by braiding once and then
--                                 commuting (`sx-through`, to come).
--
-- The runs of (B) have decreasing tops, N−i−1 for the i-th, so a
-- letter entering the i-th run always has index at most its top; that
-- is what makes the recursion terminate.
--
-- Bounds are carried as `∀ t → t < k → suc (d + t) < N`, one per
-- letter of the run, which is what the induction needs at each step.

private
  Bounds : ℕ → ℕ → Set
  Bounds d k = ∀ t → t < k → suc (d + t) < N

  bounds-tl : ∀ {d k} → Bounds d (suc k) → Bounds (suc d) k
  bounds-tl {d} {k} b t lt =
    Eq.subst (λ z → suc z < N) (+-suc d t) (b (suc t) (s≤s lt))

  bounds-hd : ∀ {d k} → Bounds d (suc k) → suc d < N
  bounds-hd {d} b = Eq.subst (λ z → suc z < N) (+-identityʳ d) (b 0 (s≤s z≤n))

  d+1 : ∀ (d : ℕ) → d + 1 ≡ suc d
  d+1 d = Eq.trans (+-suc d 0) (Eq.cong suc (+-identityʳ d))

-- A letter below a run, by two or more, commutes with all of it.
sx-below : ∀ (j d k : ℕ) → suc j < N → Bounds d k → suc j < d →
           sx j • runFrom d k ≈ runFrom d k • sx j
sx-below j d zero    jN b lt = trans right-unit (sym left-unit)
sx-below j d (suc k) jN b lt = begin
  sx j • (sx d • runFrom (suc d) k)
    ≈⟨ sym assoc ⟩
  (sx j • sx d) • runFrom (suc d) k
    ≈⟨ front _ (sym (sx-far j d (<-trans (n<1+n j) jN) jN
                            (<-trans (n<1+n d) (bounds-hd b)) (bounds-hd b) lt)) ⟩
  (sx d • sx j) • runFrom (suc d) k
    ≈⟨ assoc ⟩
  sx d • (sx j • runFrom (suc d) k)
    ≈⟨ back _ (sx-below j (suc d) k jN (bounds-tl b) (<-trans lt (n<1+n d))) ⟩
  sx d • (runFrom (suc d) k • sx j)
    ≈⟨ sym assoc ⟩
  (sx d • runFrom (suc d) k) • sx j ∎

-- A letter just below a run extends it.  This is definitional: the run
-- is built by consing its first letter.
sx-extend : ∀ (d k : ℕ) → sx d • runFrom (suc d) k ≡ runFrom d (suc k)
sx-extend d k = Eq.refl

-- A letter at the start of a run turns the first two into a sign.
sx-absorb : ∀ (d k : ℕ) → Bounds d (suc k) →
            sx d • runFrom d (suc k) ≈ zzℕ d (suc d) • runFrom (suc d) k
sx-absorb d k b = begin
  sx d • (sx d • runFrom (suc d) k)
    ≈⟨ sym assoc ⟩
  (sx d • sx d) • runFrom (suc d) k
    ≈⟨ front _ (sx-square d (<-trans (n<1+n d) (bounds-hd b)) (bounds-hd b)) ⟩
  zzℕ d (suc d) • runFrom (suc d) k ∎

-- A letter inside a run passes through it and comes out one lower.
-- The letter meets its neighbour once, where it braids, and commutes
-- with everything else; the braid leaves the lowered letter behind,
-- which then commutes out to the right.
--
-- The induction is on the *gap* between the letter and the run's
-- first index, which is what decreases as the head is stripped off.
-- Deciding whether the letter is the head's neighbour instead would
-- put the recursive call under a `with`, where the termination
-- checker loses the connection.
sx-through : ∀ (g d k : ℕ) → suc (suc (g + d)) < N → Bounds d k →
             suc (suc (g + d)) ≤ d + k →
             sx (suc (g + d)) • runFrom d k ≈ runFrom d k • sx (g + d)
sx-through zero d zero jN b lt =
  ⊥-elim (n≮n d (≤-trans (n≤1+n (suc d))
                         (Eq.subst (suc (suc d) ≤_) (+-identityʳ d) lt)))
sx-through zero d (suc zero) jN b lt =
  ⊥-elim (n≮n (suc d) (Eq.subst (suc (suc d) ≤_) (d+1 d) lt))
sx-through zero d (suc (suc k)) jN b lt = begin
  sx (suc d) • (sx d • (sx (suc d) • R))
    ≈⟨ back _ (sym assoc) ⟩
  sx (suc d) • ((sx d • sx (suc d)) • R)
    ≈⟨ sym assoc ⟩
  (sx (suc d) • (sx d • sx (suc d))) • R
    ≈⟨ front _ (sym (sx-braid d dN sdN jN)) ⟩
  (sx d • (sx (suc d) • sx d)) • R
    ≈⟨ assoc ⟩
  sx d • ((sx (suc d) • sx d) • R)
    ≈⟨ back _ assoc ⟩
  sx d • (sx (suc d) • (sx d • R))
    ≈⟨ back _ (back _ (sx-below d (suc (suc d)) k sdN
                                (bounds-tl (bounds-tl b)) (n<1+n (suc d)))) ⟩
  sx d • (sx (suc d) • (R • sx d))
    ≈⟨ back _ (sym assoc) ⟩
  sx d • ((sx (suc d) • R) • sx d)
    ≈⟨ sym assoc ⟩
  (sx d • (sx (suc d) • R)) • sx d ∎
  where
  R   = runFrom (suc (suc d)) k
  sdN = <-trans (n<1+n (suc d)) jN
  dN  = <-trans (n<1+n d) sdN
sx-through (suc g) d zero jN b lt =
  ⊥-elim (n≮n (g + d)
    (≤-trans (≤-trans (n≤1+n (suc (g + d))) (n≤1+n (suc (suc (g + d)))))
             (≤-trans (Eq.subst (suc (suc (suc (g + d))) ≤_) (+-identityʳ d) lt)
                      (m≤n+m d g))))
sx-through (suc g) d (suc k) jN b lt = begin
  sx (suc (suc (g + d))) • (sx d • R)
    ≈⟨ sym assoc ⟩
  (sx (suc (suc (g + d))) • sx d) • R
    ≈⟨ front _ (sx-far d (suc (suc (g + d))) dN sdN sgN jN
                       (s≤s (s≤s (m≤n+m d g)))) ⟩
  (sx d • sx (suc (suc (g + d)))) • R
    ≈⟨ assoc ⟩
  sx d • (sx (suc (suc (g + d))) • R)
    ≈⟨ back _ ih ⟩
  sx d • (R • sx (suc (g + d)))
    ≈⟨ sym assoc ⟩
  (sx d • R) • sx (suc (g + d)) ∎
  where
  R   = runFrom (suc d) k
  sdN = bounds-hd b
  dN  = <-trans (n<1+n d) sdN
  sgN = <-trans (n<1+n (suc (suc (g + d)))) jN
  e   = +-suc g d
  ih  : sx (suc (suc (g + d))) • R ≈ R • sx (suc (g + d))
  ih  = Eq.subst (λ z → sx (suc z) • R ≈ R • sx z) e
          (sx-through g (suc d) k
            (Eq.subst (λ z → suc (suc z) < N) (Eq.sym e) jN)
            (bounds-tl b)
            (Eq.subst (λ z → suc (suc z) ≤ suc d + k) (Eq.sym e)
              (Eq.subst (suc (suc (suc (g + d))) ≤_) (+-suc d k) lt)))

-- The same with the letter named rather than the gap.
sx-inside : ∀ (j d k : ℕ) → suc (suc j) < N → Bounds d k →
            d ≤ j → suc (suc j) ≤ d + k →
            sx (suc j) • runFrom d k ≈ runFrom d k • sx j
sx-inside j d k jN b dj lt =
  Eq.subst (λ z → sx (suc z) • runFrom d k ≈ runFrom d k • sx z) e
    (sx-through (j ∸ d) d k
      (Eq.subst (λ z → suc (suc z) < N) (Eq.sym e) jN)
      b
      (Eq.subst (λ z → suc (suc z) ≤ d + k) (Eq.sym e) lt))
  where
  e : j ∸ d + d ≡ j
  e = m∸n+n≡m dj

------------------------------------------------------------------------
-- Arithmetic
--
-- Four facts about truncated subtraction, and that N is positive.
-- They are what the run lengths of (B) need: the i-th run has
-- N − i − dᵢ letters, and stripping its first letter off lowers that
-- by one.

private
  pred≤ : ∀ {a b : ℕ} → suc a ≤ suc b → a ≤ b
  pred≤ (s≤s le) = le

  ∸suc′ : ∀ (M j : ℕ) → suc j ≤ M → M ∸ j ≡ suc (M ∸ suc j)
  ∸suc′ zero    j       ()
  ∸suc′ (suc M) zero    le       = Eq.refl
  ∸suc′ (suc M) (suc j) (s≤s le) = ∸suc′ M j le

  ∸-shift : ∀ (P i : ℕ) → P ∸ suc i ≡ (P ∸ i) ∸ 1
  ∸-shift zero    zero    = Eq.refl
  ∸-shift zero    (suc i) = Eq.refl
  ∸-shift (suc P) zero    = Eq.refl
  ∸-shift (suc P) (suc i) = ∸-shift P i

  suc∸1 : ∀ (j : ℕ) → 0 < j → suc (j ∸ 1) ≡ j
  suc∸1 zero    ()
  suc∸1 (suc j) _ = Eq.refl

  2^pos : ∀ (n : ℕ) → 0 < 2 ^ℕ n
  2^pos zero = s≤s z≤n
  2^pos (suc n) with 2 ^ℕ n | 2^pos n
  ... | zero  | ()
  ... | suc x | _ = s≤s z≤n

  0<N : 0 < N
  0<N = 2^pos (₃₊ m)

  bump : ∀ (P : ℕ) → 0 < P → ∀ (x : ℕ) → x < P ∸ 1 → suc x < P
  bump zero    ()
  bump (suc P) _  x lt = s≤s lt

-- One run less means one index more.
shift-Ni : ∀ (i k : ℕ) → N ∸ i ≡ suc k → N ∸ suc i ≡ k
shift-Ni i k Ni = Eq.trans (∸-shift N i) (Eq.cong (_∸ 1) Ni)

-- The i-th run, with its length read off the number of runs left.
runAt≡ : ∀ (i v : ℕ) {k : ℕ} → N ∸ i ≡ k → runAt i v ≡ runFrom v (k ∸ v)
runAt≡ i v Ni = Eq.cong (λ z → runFrom v (z ∸ v)) Ni

-- Every letter of the i-th run is a letter of the alphabet.
run-bounds : ∀ (i k v : ℕ) → 1 ≤ i → N ∸ i ≡ k → v ≤ k → Bounds v (k ∸ v)
run-bounds i k v 1i Ni vk t lt = bump N 0<N (v + t) v+t<N-1
  where
  v+t<k : v + t < k
  v+t<k = Eq.subst (v + t <_) (m+[n∸m]≡n vk) (+-monoʳ-< v lt)

  k≤N-1 : k ≤ N ∸ 1
  k≤N-1 = ≤-trans (≤-reflexive (Eq.sym Ni)) (∸-monoʳ-≤ N 1i)

  v+t<N-1 : v + t < N ∸ 1
  v+t<N-1 = <-≤-trans v+t<k k≤N-1

-- An index of a letter that the i-th run can hold.
idx-bound : ∀ (i k j : ℕ) → 1 ≤ i → N ∸ i ≡ k → suc j ≤ k → suc j < N
idx-bound i k j 1i Ni sj =
  bump N 0<N j (≤-trans sj (≤-trans (≤-reflexive (Eq.sym Ni)) (∸-monoʳ-≤ N 1i)))

------------------------------------------------------------------------
-- Changing one entry of a code

upd : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)
upd d i v t with t ≟ⁿ i
... | yes _ = v
... | no  _ = d t

upd-at : ∀ (d : ℕ → ℕ) (i v : ℕ) → upd d i v i ≡ v
upd-at d i v with i ≟ⁿ i
... | yes _  = Eq.refl
... | no  ne = ⊥-elim (ne Eq.refl)

upd-off : ∀ (d : ℕ → ℕ) (i v t : ℕ) → t ≢ i → upd d i v t ≡ d t
upd-off d i v t ne with t ≟ⁿ i
... | yes e = ⊥-elim (ne e)
... | no  _ = Eq.refl

Lehmer-upd : ∀ (d : ℕ → ℕ) (i v : ℕ) → Lehmer d → v ≤ N ∸ i → Lehmer (upd d i v)
Lehmer-upd d i v L le t = go (t ≟ⁿ i)
  where
  -- Deciding here rather than with a `with`, which would rewrite the
  -- goal into the shape of `upd`'s own case split.
  go : Dec (t ≡ i) → upd d i v t ≤ N ∸ t
  go (yes Eq.refl) = Eq.subst (_≤ N ∸ t) (Eq.sym (upd-at d t v)) le
  go (no  ne)      = Eq.subst (_≤ N ∸ t) (Eq.sym (upd-off d i v t ne)) (L t)

-- The runs from the i-th on read only the entries from the i-th on.
permFrom-ext : ∀ (i k : ℕ) (d d′ : ℕ → ℕ) → (∀ t → i ≤ t → d t ≡ d′ t) →
               permFrom i k d ≡ permFrom i k d′
permFrom-ext i zero    d d′ ag = Eq.refl
permFrom-ext i (suc k) d d′ ag =
  Eq.cong₂ _•_ (Eq.cong (runAt i) (ag i ≤-refl))
               (permFrom-ext (suc i) k d d′ (λ t le → ag t (≤-trans (n≤1+n i) le)))

-- An equality of words is an equivalence of them.
refl≡ : ∀ {w v : W} → w ≡ v → w ≈ v
refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- A sign letter passes a run
--
-- A mixed letter transposes the two indices of a sign pair, (58)–(62),
-- so a sign letter moves left through a run and comes out a sign
-- letter again.  *Which* one does not matter here: the side conditions
-- on the sign part are kept by toggling any two indices at all.

record PastP (w : W) (x y : Fin N) : Set where
  constructor pastP
  field
    ix iy : Fin N
    law   : w • zz x y ≈ zz ix iy • w

run-pastP : ∀ (d k : ℕ) → Bounds d k → ∀ (x y : Fin N) → PastP (runFrom d k) x y
run-pastP d zero    b x y = pastP x y (trans left-unit (sym right-unit))
run-pastP d (suc k) b x y = pastP (Conj.fst cj) (Conj.snd cj) eq
  where
  R   = runFrom (suc d) k
  p   = run-pastP (suc d) k (bounds-tl b) x y
  sdN = bounds-hd b
  dN  = <-trans (n<1+n d) sdN
  cj  = conj-any (fin d dN) (fin (suc d) sdN) (PastP.ix p) (PastP.iy p)
                 (fin≢ dN sdN (n≢sn d))

  law′ : sx d • zz (PastP.ix p) (PastP.iy p) ≈ zz (Conj.fst cj) (Conj.snd cj) • sx d
  law′ rewrite sx-zx d dN sdN = Conj.law cj

  eq : (sx d • R) • zz x y ≈ zz (Conj.fst cj) (Conj.snd cj) • (sx d • R)
  eq = begin
    (sx d • R) • zz x y                        ≈⟨ assoc ⟩
    sx d • (R • zz x y)                        ≈⟨ back _ (PastP.law p) ⟩
    sx d • (zz (PastP.ix p) (PastP.iy p) • R)  ≈⟨ sym assoc ⟩
    (sx d • zz (PastP.ix p) (PastP.iy p)) • R  ≈⟨ front _ law′ ⟩
    (zz (Conj.fst cj) (Conj.snd cj) • sx d) • R ≈⟨ assoc ⟩
    zz (Conj.fst cj) (Conj.snd cj) • (sx d • R) ∎

------------------------------------------------------------------------
-- The sign a letter leaves behind
--
-- Pushing one letter into the permutation part emits at most one sign
-- letter — the square of (23), when the letter lands on the start of
-- a run.  It is carried as `Sgn` rather than as a word so that the
-- cases where nothing is emitted stay silent.

data Sgn : Set where
  none : Sgn
  some : Fin N → Fin N → Sgn

wrd : Sgn → W
wrd none       = ε
wrd (some x y) = zz x y

app : Sgn → List (Fin N) → List (Fin N)
app none       l = l
app (some x y) l = toggle x (toggle y l)

app-Incr : ∀ (s : Sgn) (l : List (Fin N)) → Incr₀ l → Incr₀ (app s l)
app-Incr none       l i = i
app-Incr (some x y) l i = toggle²-Incr x y l i

app-Even : ∀ (s : Sgn) (l : List (Fin N)) → Even l → Even (app s l)
app-Even none       l e = e
app-Even (some x y) l e = toggle²-Even x y l e

app-atoms : ∀ (s : Sgn) (l : List (Fin N)) → wrd s • atoms l ≈ atoms (app s l)
app-atoms none       l = left-unit
app-atoms (some x y) l = merge-zz x y l

-- A run lets any such sign through.
record PastS (w : W) (s : Sgn) : Set where
  constructor pastS
  field
    out : Sgn
    law : w • wrd s ≈ wrd out • w

run-past : ∀ (d k : ℕ) → Bounds d k → (s : Sgn) → PastS (runFrom d k) s
run-past d k b none       = pastS none (trans right-unit (sym left-unit))
run-past d k b (some x y) = pastS (some (PastP.ix p) (PastP.iy p)) (PastP.law p)
  where p = run-pastP d k b x y

-- And lets it through from the middle of a product.
past-mid : ∀ (w : W) (s : Sgn) (ps : PastS w s) (P : W) →
           w • (wrd s • P) ≈ wrd (PastS.out ps) • (w • P)
past-mid w s ps P = begin
  w • (wrd s • P)               ≈⟨ sym assoc ⟩
  (w • wrd s) • P               ≈⟨ front _ (PastS.law ps) ⟩
  (wrd (PastS.out ps) • w) • P  ≈⟨ assoc ⟩
  wrd (PastS.out ps) • (w • P) ∎

------------------------------------------------------------------------
-- Pushing a letter into the permutation part
--
-- A word is reduced from the right, so each letter arrives on the
-- *left* of what is already normal.  Where it lands is decided by the
-- run it meets: it commutes past a run starting two or more above it,
-- extends one starting just above it, squares into a sign against one
-- starting at it, and passes through one starting below it, coming out
-- one lower for the next run.
--
-- The runs of (B) have tops N−i−1, which decrease, so a letter
-- entering the i-th run always has index at most that top; when it
-- reaches the last run it is `sx 0` and must land.  That is the
-- content of the hypothesis `suc j ≤ k`, k being the number of runs
-- left: at k = 0 there is nothing to prove because there is no such
-- letter.
--
-- The recursion is on fuel, not on the number of runs, because the
-- case split is a `with` and the termination checker does not see
-- through one to the recursive call.

record Absorbed (i k j : ℕ) (d : ℕ → ℕ) : Set where
  constructor absorbed
  field
    sgn    : Sgn
    code   : ℕ → ℕ
    law    : sx j • permFrom i k d ≈ wrd sgn • permFrom i k code
    lehmer : Lehmer code
    below  : ∀ t → t < i → code t ≡ d t

private
  -- An index below the current one is not the current one.
  off : ∀ {t i : ℕ} → t < i → t ≢ i
  off {t} {i} lt e = n≮n i (Eq.subst (_< i) e lt)

  -- Nor is one above it.
  off′ : ∀ {t i : ℕ} → i < t → t ≢ i
  off′ {t} {i} lt e = n≮n i (Eq.subst (i <_) e lt)

absorb-fuel : ∀ (f i k j : ℕ) (d : ℕ → ℕ) →
              k ≤ f → 1 ≤ i → N ∸ i ≡ k → suc j ≤ k → Lehmer d →
              Absorbed i k j d
absorb-fuel f       i zero    j d fk       1i Ni ()  L
absorb-fuel zero    i (suc k) j d ()       1i Ni sj  L
absorb-fuel (suc f) i (suc k) j d (s≤s fk) 1i Ni sj  L with <-cmp (suc j) (d i)
-- The run starts two or more above the letter: it commutes past.
... | tri< lt _ _ =
  absorbed (PastS.out ps) c eq (Absorbed.lehmer ih)
           (λ t t<i → Absorbed.below ih t (<-trans t<i (n<1+n i)))
  where
  v   = d i
  P   = permFrom (suc i) k d
  vk  : v ≤ suc k
  vk  = Eq.subst (v ≤_) Ni (L i)
  ih  = absorb-fuel f (suc i) k j d fk (s≤s z≤n) (shift-Ni i k Ni)
                    (pred≤ (≤-trans lt vk)) L
  c   = Absorbed.code ih
  s   = Absorbed.sgn ih
  P′  = permFrom (suc i) k c
  bd  : Bounds v (suc k ∸ v)
  bd  = run-bounds i (suc k) v 1i Ni vk
  ps  : PastS (runAt i v) s
  ps  = Eq.subst (λ w → PastS w s) (Eq.sym (runAt≡ i v Ni))
                 (run-past v (suc k ∸ v) bd s)
  sjN = idx-bound i (suc k) j 1i Ni sj
  pass : sx j • runAt i v ≈ runAt i v • sx j
  pass = Eq.subst (λ w → sx j • w ≈ w • sx j) (Eq.sym (runAt≡ i v Ni))
                  (sx-below j v (suc k ∸ v) sjN bd lt)

  chain : sx j • (runAt i v • P) ≈ wrd (PastS.out ps) • (runAt i v • P′)
  chain = begin
    sx j • (runAt i v • P)                 ≈⟨ sym assoc ⟩
    (sx j • runAt i v) • P                 ≈⟨ front _ pass ⟩
    (runAt i v • sx j) • P                 ≈⟨ assoc ⟩
    runAt i v • (sx j • P)                 ≈⟨ back _ (Absorbed.law ih) ⟩
    runAt i v • (wrd s • P′)               ≈⟨ past-mid (runAt i v) s ps P′ ⟩
    wrd (PastS.out ps) • (runAt i v • P′) ∎

  eq : sx j • permFrom i (suc k) d ≈ wrd (PastS.out ps) • permFrom i (suc k) c
  eq = Eq.subst (λ w → sx j • (runAt i v • P) ≈ wrd (PastS.out ps) • (w • P′))
                (Eq.cong (runAt i) (Eq.sym (Absorbed.below ih i (n<1+n i))))
                chain
-- The run starts just above the letter: the letter extends it.
... | tri≈ _ e _ = absorbed none c eq lem bel
  where
  v  = d i
  P  = permFrom (suc i) k d
  c  = upd d i j
  P′ = permFrom (suc i) k c

  P≡ : P ≡ P′
  P≡ = permFrom-ext (suc i) k d c
         (λ t le → Eq.sym (upd-off d i j t (off′ (<-≤-trans (n<1+n i) le))))

  ext : sx j • runAt i v ≡ runAt i (c i)
  ext = Eq.trans
          (Eq.trans (Eq.cong (sx j •_)
                      (Eq.trans (runAt≡ i v Ni)
                                (Eq.cong (λ z → runFrom z (suc k ∸ z)) (Eq.sym e))))
                    (Eq.sym (Eq.trans (runAt≡ i j Ni)
                                      (Eq.cong (runFrom j) (∸suc′ (suc k) j sj)))))
          (Eq.cong (runAt i) (Eq.sym (upd-at d i j)))

  eq : sx j • permFrom i (suc k) d ≈ wrd none • permFrom i (suc k) c
  eq = begin
    sx j • (runAt i v • P)      ≈⟨ sym assoc ⟩
    (sx j • runAt i v) • P      ≈⟨ refl≡ (Eq.cong₂ _•_ ext P≡) ⟩
    runAt i (c i) • P′          ≈⟨ sym left-unit ⟩
    ε • (runAt i (c i) • P′)   ∎

  lem : Lehmer c
  lem = Lehmer-upd d i j L
          (≤-trans (n≤1+n j) (Eq.subst (_≤ N ∸ i) (Eq.sym e) (L i)))

  bel : ∀ t → t < i → c t ≡ d t
  bel t t<i = upd-off d i j t (off t<i)
-- The run starts at the letter or below it.
absorb-fuel (suc f) i (suc k) j d (s≤s fk) 1i Ni sj L | tri> _ _ gt
  with d i ≟ⁿ j
-- At it: the square is a sign, (23), and the run loses its first letter.
absorb-fuel (suc f) i (suc k) j d (s≤s fk) 1i Ni sj L | tri> _ _ gt | yes e =
  absorbed (some (fin j jN) (fin (suc j) sjN)) c eq lem bel
  where
  v   = d i
  P   = permFrom (suc i) k d
  c   = upd d i (suc j)
  P′  = permFrom (suc i) k c
  L′  = suc k ∸ suc j
  sjN = idx-bound i (suc k) j 1i Ni sj
  jN  = <-trans (n<1+n j) sjN

  bd : Bounds j (suc L′)
  bd = Eq.subst (Bounds j) (∸suc′ (suc k) j sj)
                (run-bounds i (suc k) j 1i Ni (≤-trans (n≤1+n j) sj))

  rA : runAt i v ≡ runFrom j (suc L′)
  rA = Eq.trans (runAt≡ i v Ni)
                (Eq.trans (Eq.cong (λ z → runFrom z (suc k ∸ z)) e)
                          (Eq.cong (runFrom j) (∸suc′ (suc k) j sj)))

  P≡ : P ≡ P′
  P≡ = permFrom-ext (suc i) k d c
         (λ t le → Eq.sym (upd-off d i (suc j) t (off′ (<-≤-trans (n<1+n i) le))))

  eq : sx j • permFrom i (suc k) d ≈
       wrd (some (fin j jN) (fin (suc j) sjN)) • permFrom i (suc k) c
  eq = begin
    sx j • (runAt i v • P)
      ≈⟨ sym assoc ⟩
    (sx j • runAt i v) • P
      ≈⟨ front _ (refl≡ (Eq.cong (sx j •_) rA)) ⟩
    (sx j • runFrom j (suc L′)) • P
      ≈⟨ front _ (sx-absorb j L′ bd) ⟩
    (zzℕ j (suc j) • runFrom (suc j) L′) • P
      ≈⟨ front _ (refl≡ (Eq.cong₂ _•_ (zzℕ-fin j jN sjN)
                                      (Eq.sym (runAt≡ i (suc j) Ni)))) ⟩
    (zz (fin j jN) (fin (suc j) sjN) • runAt i (suc j)) • P
      ≈⟨ assoc ⟩
    zz (fin j jN) (fin (suc j) sjN) • (runAt i (suc j) • P)
      ≈⟨ back _ (refl≡ (Eq.cong₂ _•_ (Eq.cong (runAt i) (Eq.sym (upd-at d i (suc j))))
                                     P≡)) ⟩
    zz (fin j jN) (fin (suc j) sjN) • (runAt i (c i) • P′) ∎

  lem : Lehmer c
  lem = Lehmer-upd d i (suc j) L (Eq.subst (suc j ≤_) (Eq.sym Ni) sj)

  bel : ∀ t → t < i → c t ≡ d t
  bel t t<i = upd-off d i (suc j) t (off t<i)
-- Below it: the letter passes through and comes out one lower.
absorb-fuel (suc f) i (suc k) j d (s≤s fk) 1i Ni sj L | tri> _ _ gt | no ne =
  absorbed (PastS.out ps) c eq (Absorbed.lehmer ih)
           (λ t t<i → Absorbed.below ih t (<-trans t<i (n<1+n i)))
  where
  v   = d i
  P   = permFrom (suc i) k d
  vk  : v ≤ suc k
  vk  = Eq.subst (v ≤_) Ni (L i)
  v<j : v < j
  v<j = ≤∧≢⇒< (pred≤ gt) ne
  j≡  : suc (j ∸ 1) ≡ j
  j≡  = suc∸1 j (≤-<-trans z≤n v<j)
  sjN = idx-bound i (suc k) j 1i Ni sj

  ih  = absorb-fuel f (suc i) k (j ∸ 1) d fk (s≤s z≤n) (shift-Ni i k Ni)
                    (Eq.subst (_≤ k) (Eq.sym j≡) (pred≤ sj)) L
  c   = Absorbed.code ih
  s   = Absorbed.sgn ih
  P′  = permFrom (suc i) k c
  bd  : Bounds v (suc k ∸ v)
  bd  = run-bounds i (suc k) v 1i Ni vk
  ps  : PastS (runAt i v) s
  ps  = Eq.subst (λ w → PastS w s) (Eq.sym (runAt≡ i v Ni))
                 (run-past v (suc k ∸ v) bd s)

  thr : sx j • runAt i v ≈ runAt i v • sx (j ∸ 1)
  thr = Eq.subst (λ z → sx z • runAt i v ≈ runAt i v • sx (j ∸ 1)) j≡
          (Eq.subst (λ w → sx (suc (j ∸ 1)) • w ≈ w • sx (j ∸ 1))
                    (Eq.sym (runAt≡ i v Ni))
                    (sx-inside (j ∸ 1) v (suc k ∸ v)
                      (Eq.subst (λ z → suc z < N) (Eq.sym j≡) sjN)
                      bd
                      (pred≤ (Eq.subst (suc v ≤_) (Eq.sym j≡) v<j))
                      (Eq.subst (λ z → suc z ≤ v + (suc k ∸ v)) (Eq.sym j≡)
                        (Eq.subst (suc j ≤_) (Eq.sym (m+[n∸m]≡n vk)) sj))))

  chain : sx j • (runAt i v • P) ≈ wrd (PastS.out ps) • (runAt i v • P′)
  chain = begin
    sx j • (runAt i v • P)                 ≈⟨ sym assoc ⟩
    (sx j • runAt i v) • P                 ≈⟨ front _ thr ⟩
    (runAt i v • sx (j ∸ 1)) • P           ≈⟨ assoc ⟩
    runAt i v • (sx (j ∸ 1) • P)           ≈⟨ back _ (Absorbed.law ih) ⟩
    runAt i v • (wrd s • P′)               ≈⟨ past-mid (runAt i v) s ps P′ ⟩
    wrd (PastS.out ps) • (runAt i v • P′) ∎

  eq : sx j • permFrom i (suc k) d ≈ wrd (PastS.out ps) • permFrom i (suc k) c
  eq = Eq.subst (λ w → sx j • (runAt i v • P) ≈ wrd (PastS.out ps) • (w • P′))
                (Eq.cong (runAt i) (Eq.sym (Absorbed.below ih i (n<1+n i))))
                chain

-- The letter pushed into the permutation part of (B).
absorb-perm : ∀ (j : ℕ) (d : ℕ → ℕ) → suc j ≤ N ∸ 1 → Lehmer d →
              Absorbed 1 (N ∸ 1) j d
absorb-perm j d sj L = absorb-fuel (N ∸ 1) 1 (N ∸ 1) j d ≤-refl ≤-refl Eq.refl sj L

------------------------------------------------------------------------
-- A letter passes the sign part
--
-- A mixed letter transposes the two indices of a sign pair, so it
-- passes a sign part written as a product of *pairs* and leaves a
-- product of pairs behind.  The recursion is on `signOf`, two indices
-- at a time, rather than on `atoms`, one at a time: an atom is a pair
-- through the index 1, which the letter may move, so one atom need not
-- come out as one atom — but a pair always comes out as a pair, and
-- with it the parity that the sign part's side condition needs.

record PastSign (j : ℕ) (l : List (Fin N)) : Set where
  constructor pastSign
  field
    out  : List (Fin N)
    law  : sx j • signOf l ≈ atoms out • sx j
    incr : Incr₀ out
    even : Even out

sx-past : ∀ (j : ℕ) (jN : j < N) (sjN : suc j < N) (l : List (Fin N)) →
          Incr₀ l → Even l → PastSign j l
sx-past j jN sjN []      i₀ nil       = pastSign [] (trans right-unit (sym left-unit)) nil nil
sx-past j jN sjN (a ∷ []) i₀ (cons ())
sx-past j jN sjN (a ∷ b ∷ l) (cons (cons _ i)) (cons (cons e)) =
  pastSign (toggle p (toggle q out)) law′
           (toggle²-Incr p q out (PastSign.incr ih))
           (toggle²-Even p q out (PastSign.even ih))
  where
  ih  = sx-past j jN sjN l (Incr⇒Incr₀ i) e
  out = PastSign.out ih
  cj  = conj-any (fin j jN) (fin (suc j) sjN) a b (fin≢ jN sjN (n≢sn j))
  p   = Conj.fst cj
  q   = Conj.snd cj

  step : sx j • zz a b ≈ zz p q • sx j
  step rewrite sx-zx j jN sjN = Conj.law cj

  law′ : sx j • (zz a b • signOf l) ≈ atoms (toggle p (toggle q out)) • sx j
  law′ = begin
    sx j • (zz a b • signOf l)              ≈⟨ sym assoc ⟩
    (sx j • zz a b) • signOf l              ≈⟨ front _ step ⟩
    (zz p q • sx j) • signOf l              ≈⟨ assoc ⟩
    zz p q • (sx j • signOf l)              ≈⟨ back _ (PastSign.law ih) ⟩
    zz p q • (atoms out • sx j)             ≈⟨ sym assoc ⟩
    (zz p q • atoms out) • sx j             ≈⟨ front _ (merge-zz p q out) ⟩
    atoms (toggle p (toggle q out)) • sx j ∎

-- A sign part is central, so the sign a letter leaves behind can be
-- moved out to the left.
atoms-comm : ∀ (l : List (Fin N)) (x y : Fin N) →
             atoms l • zz x y ≈ zz x y • atoms l
atoms-comm l x y = begin
  atoms l • zz x y               ≈⟨ back _ (DE-ZZ x y) ⟩
  atoms l • (zz o₁ x • zz o₁ y)  ≈⟨ sym assoc ⟩
  (atoms l • zz o₁ x) • zz o₁ y  ≈⟨ front _ (atoms-zz l x) ⟩
  (zz o₁ x • atoms l) • zz o₁ y  ≈⟨ assoc ⟩
  zz o₁ x • (atoms l • zz o₁ y)  ≈⟨ back _ (atoms-zz l y) ⟩
  zz o₁ x • (zz o₁ y • atoms l)  ≈⟨ sym assoc ⟩
  (zz o₁ x • zz o₁ y) • atoms l  ≈⟨ front _ (sym (DE-ZZ x y)) ⟩
  zz x y • atoms l ∎

atoms-comm-sgn : ∀ (l : List (Fin N)) (s : Sgn) →
                 atoms l • wrd s ≈ wrd s • atoms l
atoms-comm-sgn l none       = trans right-unit (sym left-unit)
atoms-comm-sgn l (some x y) = atoms-comm l x y

------------------------------------------------------------------------
-- One letter of the permutation part, absorbed
--
-- Both halves at once: the letter passes the sign part, lands in the
-- permutation part, and the sign it leaves behind comes back out to
-- the left and merges in.

record Absorb (j : ℕ) (l : List (Fin N)) (d : ℕ → ℕ) : Set where
  constructor absorb
  field
    lis  : List (Fin N)
    code : ℕ → ℕ
    law  : sx j • NF l d ≈ NF lis code
    norm : Normal lis code

absorb-sx : ∀ (j : ℕ) (l : List (Fin N)) (d : ℕ → ℕ) →
            suc j ≤ N ∸ 1 → Normal l d → Absorb j l d
absorb-sx j l d sj nm = absorb (app s l₁) (Absorbed.code ap) law′ norm′
  where
  sjN = idx-bound 1 (N ∸ 1) j ≤-refl Eq.refl sj
  jN  = <-trans (n<1+n j) sjN
  ps  = sx-past j jN sjN l (Normal.incr nm) (Normal.even nm)
  l₁  = PastSign.out ps
  ap  = absorb-perm j d sj (Normal.lehmer nm)
  s   = Absorbed.sgn ap
  d′  = Absorbed.code ap

  norm′ : Normal (app s l₁) d′
  norm′ = normal (app-Incr s l₁ (PastSign.incr ps))
                 (app-Even s l₁ (PastSign.even ps))
                 (Absorbed.lehmer ap)

  law′ : sx j • (signOf l • permPart d) ≈ signOf (app s l₁) • permPart d′
  law′ = begin
    sx j • (signOf l • permPart d)      ≈⟨ sym assoc ⟩
    (sx j • signOf l) • permPart d      ≈⟨ front _ (PastSign.law ps) ⟩
    (atoms l₁ • sx j) • permPart d      ≈⟨ assoc ⟩
    atoms l₁ • (sx j • permPart d)      ≈⟨ back _ (Absorbed.law ap) ⟩
    atoms l₁ • (wrd s • permPart d′)    ≈⟨ sym assoc ⟩
    (atoms l₁ • wrd s) • permPart d′    ≈⟨ front _ (atoms-comm-sgn l₁ s) ⟩
    (wrd s • atoms l₁) • permPart d′    ≈⟨ front _ (app-atoms s l₁) ⟩
    atoms (app s l₁) • permPart d′
      ≈⟨ front _ (sym (signOf-atoms (app s l₁) (Normal.even norm′))) ⟩
    signOf (app s l₁) • permPart d′ ∎

------------------------------------------------------------------------
-- Existence, for a product of letters on consecutive pairs
--
-- The empty product is (B) with no signs and dᵢ = N − i, and each
-- further letter is absorbed by `absorb-sx`.  This is the second half
-- of Lemma A.4's existence: the first is that every Hadamard-free
-- generator of P is such a product, by (34), (53), (33), (52) and
-- (54).

-- Letters on consecutive pairs, written out.
sxs : List ℕ → W
sxs []      = ε
sxs (j ∷ l) = sx j • sxs l

-- Their indices are indices of letters.
data Ok : List ℕ → Set where
  nil  : Ok []
  cons : ∀ {j l} → suc j ≤ N ∸ 1 → Ok l → Ok (j ∷ l)

-- The code of the identity permutation.
idCode : ℕ → ℕ
idCode t = N ∸ t

idCode-Lehmer : Lehmer idCode
idCode-Lehmer t = ≤-refl

permFrom-id : ∀ (i k : ℕ) → permFrom i k idCode ≈ ε
permFrom-id i zero    = refl
permFrom-id i (suc k) = begin
  runAt i (N ∸ i) • permFrom (suc i) k idCode
    ≈⟨ front _ (refl≡ (Eq.cong (runFrom (N ∸ i)) (n∸n≡0 (N ∸ i)))) ⟩
  ε • permFrom (suc i) k idCode
    ≈⟨ left-unit ⟩
  permFrom (suc i) k idCode
    ≈⟨ permFrom-id (suc i) k ⟩
  ε ∎

NF-id : NF [] idCode ≈ ε
NF-id = trans left-unit (permFrom-id 1 (N ∸ 1))

record Reduced (w : W) : Set where
  constructor reduced
  field
    lis  : List (Fin N)
    code : ℕ → ℕ
    law  : w ≈ NF lis code
    norm : Normal lis code

reduce : ∀ (l : List ℕ) → Ok l → Reduced (sxs l)
reduce []      nil          = reduced [] idCode (sym NF-id) (normal nil nil idCode-Lehmer)
reduce (j ∷ l) (cons ok oks) =
  reduced (Absorb.lis ab) (Absorb.code ab)
          (trans (back _ (Reduced.law ih)) (Absorb.law ab))
          (Absorb.norm ab)
  where
  ih = reduce l oks
  ab = absorb-sx j (Reduced.lis ih) (Reduced.code ih) ok (Reduced.norm ih)

------------------------------------------------------------------------
-- Every Hadamard-free generator is a product of consecutive letters
--
-- This is the other half of Lemma A.4's existence.  The paper takes
-- (34), (53), (33), (52) and (54) for it; the route here is the same
-- reductions read straight off Figure 8:
--
--   * a sign pair is a mixed letter squared, (52) = `zx²′`, so signs
--     need no separate treatment;
--   * a mixed letter whose sign is on neither index of its pair is
--     that sign times one whose sign is on an index, (30);
--   * (33) and `flip′` put the sign on whichever index one likes;
--   * a letter on a pair at distance more than one shrinks by (25) or
--     (27), by the parity of the gap — the induction of `flip-fuel`
--     again, and the scaffolding is shared with it;
--   * and what is left on a *consecutive* pair is `sx a` or its cube,
--     the cube because `sx a` squared is the sign pair, (23).

record AsSxs (w : W) : Set where
  constructor asSxs
  field
    ixs : List ℕ
    ok  : Ok ixs
    law : w ≈ sxs ixs

Ok-++ : ∀ {l l′ : List ℕ} → Ok l → Ok l′ → Ok (l ++ l′)
Ok-++ nil        o′ = o′
Ok-++ (cons b o) o′ = cons b (Ok-++ o o′)

sxs-++ : ∀ (l l′ : List ℕ) → sxs (l ++ l′) ≈ sxs l • sxs l′
sxs-++ []      l′ = sym left-unit
sxs-++ (j ∷ l) l′ = trans (back _ (sxs-++ l l′)) (sym assoc)

AsSxs-ε : AsSxs ε
AsSxs-ε = asSxs [] nil refl

AsSxs-≈ : ∀ {u v : W} → u ≈ v → AsSxs v → AsSxs u
AsSxs-≈ e a = asSxs (AsSxs.ixs a) (AsSxs.ok a) (trans e (AsSxs.law a))

AsSxs-• : ∀ {u v : W} → AsSxs u → AsSxs v → AsSxs (u • v)
AsSxs-• p q =
  asSxs (AsSxs.ixs p ++ AsSxs.ixs q) (Ok-++ (AsSxs.ok p) (AsSxs.ok q))
        (trans (cong (AsSxs.law p) (AsSxs.law q))
               (sym (sxs-++ (AsSxs.ixs p) (AsSxs.ixs q))))

private
  down : ∀ (P x : ℕ) → x < P → x ≤ P ∸ 1
  down zero    x ()
  down (suc P) x (s≤s le) = le

  ok-ix : ∀ (a a′ : Fin N) → Succ a a′ → suc (toℕ a) ≤ N ∸ 1
  ok-ix a a′ s = down N (suc (toℕ a)) (Eq.subst (_< N) s (toℕ<n a′))

  sx-lit : ∀ (a a′ : Fin N) → Succ a a′ → zx a a a′ ≡ sx (toℕ a)
  sx-lit a a′ s =
    Eq.trans (Eq.sym (zxℕ-zx a a a′)) (Eq.cong (zxℕ (toℕ a) (toℕ a)) s)

  Succ≢ : ∀ (a a′ : Fin N) → Succ a a′ → a ≢ a′
  Succ≢ a a′ s e = n≢sn (toℕ a) (Eq.trans (Eq.cong toℕ e) s)

  fin<⇒≢ : ∀ {a b : Fin N} → toℕ a < toℕ b → a ≢ b
  fin<⇒≢ {a} {b} lt e =
    n≮n (toℕ a) (Eq.subst (toℕ a <_) (Eq.cong toℕ (Eq.sym e)) lt)

-- The letter on a consecutive pair, with its sign below.
AsSxs-sx : ∀ (a a′ : Fin N) → Succ a a′ → AsSxs (zx a a a′)
AsSxs-sx a a′ s = asSxs (toℕ a ∷ []) (cons (ok-ix a a′ s) nil)
                        (trans (refl≡ (sx-lit a a′ s)) (sym right-unit))

-- And with its sign above: the letter cubed, since its square is the
-- sign pair, (23), and the two sign choices differ by that pair.
AsSxs-sx³ : ∀ (a a′ : Fin N) → Succ a a′ → AsSxs (zx a′ a′ a)
AsSxs-sx³ a a′ s = AsSxs-≈ cube (AsSxs-• one (AsSxs-• one one))
  where
  a≢a′ = Succ≢ a a′ s
  one  = AsSxs-sx a a′ s

  cube : zx a′ a′ a ≈ zx a a a′ • (zx a a a′ • zx a a a′)
  cube = begin
    zx a′ a′ a                             ≈⟨ sym left-unit ⟩
    ε • zx a′ a′ a                         ≈⟨ front _ (sym (zz² a a′)) ⟩
    (zz a a′ • zz a a′) • zx a′ a′ a       ≈⟨ assoc ⟩
    zz a a′ • (zz a a′ • zx a′ a′ a)       ≈⟨ back _ (sym (flip′ a a′ a≢a′)) ⟩
    zz a a′ • zx a a a′                    ≈⟨ front _ (sym (zx²′ a a′ a≢a′)) ⟩
    (zx a a a′ • zx a a a′) • zx a a a′    ≈⟨ assoc ⟩
    zx a a a′ • (zx a a a′ • zx a a a′)   ∎

-- The induction on the gap, exactly `flip-fuel`'s: at even parity the
-- lower index moves up, (25); at odd parity the upper one moves down,
-- (27); a gap of one is a letter on a consecutive pair.
zx-fuel : ∀ (k : ℕ) (a c : Fin N) → toℕ a < toℕ c → toℕ c ∸ toℕ a ≤ k →
          AsSxs (zx a a c)
zx-fuel zero a c lt fu = ⊥-elim (<-irrefl Eq.refl (≤-trans (0<∸ lt) fu))
zx-fuel (suc k) a c lt fu with suc (toℕ a) <? toℕ c
... | no ¬p = AsSxs-sx a c (≤-antisym (≮⇒≥ ¬p) lt)
... | yes p with parity (toℕ c ∸ toℕ a) in eq
...         | true =
  let pa : suc (toℕ a) < N
      pa = <-trans p (toℕ<n c)
      a′ = next a pa
      sa : Succ a a′
      sa = next-Succ a pa
      lt′ : toℕ a′ < toℕ c
      lt′ = Eq.subst (_< toℕ c) (Eq.sym sa) p
      fu′ : toℕ c ∸ toℕ a′ ≤ k
      fu′ = Eq.subst (λ z → toℕ c ∸ z ≤ k) (Eq.sym sa)
              (Eq.subst (_≤ k) (Eq.sym (∸suc (toℕ c) (toℕ a))) (pred≤pred fu))
  in AsSxs-≈ (axiom (r25 a a′ c sa lt′ eq))
             (AsSxs-• (AsSxs-≈ (axiom (r33 a′ a)) (AsSxs-sx³ a a′ sa))
                      (AsSxs-• (zx-fuel k a′ c lt′ fu′) (AsSxs-sx a a′ sa)))
...         | false =
  let 0<c : 0 < toℕ c
      0<c = ≤-trans (s≤s z≤n) lt
      c′ = prev c
      sc : Succ c′ c
      sc = prev-Succ c 0<c
      lt″ : toℕ a < toℕ c′
      lt″ = pred≤ (Eq.subst (suc (toℕ a) <_) sc p)
      fu″ : toℕ c′ ∸ toℕ a ≤ k
      fu″ = Eq.subst (λ z → z ∸ toℕ a ≤ k) (Eq.sym (prev-toℕ c))
              (Eq.subst (_≤ k) (Eq.sym (pred∸ (toℕ c) (toℕ a))) (pred≤pred fu))
  in AsSxs-≈ (axiom (r27 a c′ c sc p eq))
             (AsSxs-• (AsSxs-sx c′ c sc)
                      (AsSxs-• (zx-fuel k a c′ lt″ fu″)
                               (AsSxs-≈ (axiom (r33 c c′)) (AsSxs-sx³ c′ c sc))))

-- A mixed letter whose sign is on the lower index of its pair.
AsSxs-zx-lo : ∀ (a c : Fin N) → toℕ a < toℕ c → AsSxs (zx a a c)
AsSxs-zx-lo a c lt = zx-fuel (toℕ c ∸ toℕ a) a c lt ≤-refl

-- A sign pair, by (52); (20) and (21) put it the right way round.
private
  zz-lo : ∀ (a b : Fin N) → toℕ a < toℕ b → AsSxs (zz a b)
  zz-lo a b lt = AsSxs-≈ (sym (zx²′ a b (fin<⇒≢ lt))) (AsSxs-• inner inner)
    where inner = AsSxs-zx-lo a b lt

AsSxs-zz : ∀ (a b : Fin N) → AsSxs (zz a b)
AsSxs-zz a b with <-cmp (toℕ a) (toℕ b)
... | tri< lt _ _ = zz-lo a b lt
... | tri≈ _ e _  =
  AsSxs-≈ (trans (refl≡ (Eq.cong (zz a) (Eq.sym (toℕ-injective e)))) (axiom (r20 a)))
          AsSxs-ε
... | tri> _ _ gt = AsSxs-≈ (axiom (r21 a b)) (zz-lo b a gt)

-- A mixed letter whose sign is on either index of its pair.
AsSxs-zx-own : ∀ (a b : Fin N) → a ≢ b → AsSxs (zx a a b)
AsSxs-zx-own a b a≢b with <-cmp (toℕ a) (toℕ b)
... | tri< lt _ _ = AsSxs-zx-lo a b lt
... | tri≈ _ e _  = ⊥-elim (a≢b (toℕ-injective e))
... | tri> _ _ gt =
  AsSxs-≈ (flip′ a b a≢b) (AsSxs-• (AsSxs-zz a b) (AsSxs-zx-lo b a gt))

-- And any mixed letter, by (30) when its sign is on neither index and
-- (33) when it is on the upper one.
AsSxs-zx : ∀ (c a b : Fin N) → a ≢ b → AsSxs (zx c a b)
AsSxs-zx c a b a≢b with c ≟ a | c ≟ b
... | yes Eq.refl | _           = AsSxs-zx-own a b a≢b
... | no  c≢a     | yes Eq.refl = AsSxs-≈ (axiom (r33 c a))
                                          (AsSxs-zx-own c a (λ e → a≢b (Eq.sym e)))
... | no  c≢a     | no  c≢b     =
  AsSxs-≈ (axiom (r30 c a b a≢b c≢a c≢b))
          (AsSxs-• (AsSxs-zz c a) (AsSxs-zx-own a b a≢b))

-- A double exchange, by (34).
AsSxs-xx : ∀ (a b c d : Fin N) → a ≢ b → c ≢ d → AsSxs (xx a b c d)
AsSxs-xx a b c d a≢b c≢d =
  AsSxs-≈ (axiom (r34 a b c d a≢b c≢d))
          (AsSxs-• (AsSxs-zx-own a b a≢b) (AsSxs-zx b c d c≢d))

------------------------------------------------------------------------
-- Lemma A.4, existence
--
-- A letter of P carries its distinctness side condition irrelevantly,
-- and the rules of Figure 8 need it relevantly; the two are bridged by
-- deciding it again, the irrelevant proof ruling out the branch where
-- the indices coincide.

-- A letter with no Hadamard in it.
data HFree : GenP (₃₊ m) → Set where
  hf-zz : ∀ (a b : Fin N) → HFree (−1−1 a b)
  hf-zx : ∀ (c a b : Fin N) .(ni : a ≢ b) → HFree (−1X c a b ni)
  hf-xx : ∀ (a b c d : Fin N) .(ni : a ≢ b) .(ni′ : c ≢ d) →
          HFree (XX a b c d ni ni′)

-- A word of such letters.
data HFreeʷ : W → Set where
  gen : ∀ {g} → HFree g → HFreeʷ [ g ]ʷ
  nil : HFreeʷ ε
  cat : ∀ {u v} → HFreeʷ u → HFreeʷ v → HFreeʷ (u • v)

-- The deciding wrapper on indices already known to differ.
gen-zx : ∀ (c a b : Fin N) .(ni : a ≢ b) → [ −1X {₃₊ m} c a b ni ]ʷ ≡ zx {₃₊ m} c a b
gen-zx c a b ni with a ≟ b
... | yes e = ⊥-elim-irr (ni e)
... | no  _ = Eq.refl

gen-xx : ∀ (a b c d : Fin N) .(ni : a ≢ b) .(ni′ : c ≢ d) →
         [ XX {₃₊ m} a b c d ni ni′ ]ʷ ≡ xx {₃₊ m} a b c d
gen-xx a b c d ni ni′ with a ≟ b | c ≟ d
... | yes e | _     = ⊥-elim-irr (ni e)
... | no  _ | yes e = ⊥-elim-irr (ni′ e)
... | no  _ | no  _ = Eq.refl

AsSxs-gen : ∀ {g : GenP (₃₊ m)} → HFree g → AsSxs [ g ]ʷ
AsSxs-gen (hf-zz a b) = AsSxs-zz a b
AsSxs-gen (hf-zx c a b ni) with a ≟ b
... | yes e  = ⊥-elim-irr (ni e)
... | no  ne = AsSxs-≈ (refl≡ (gen-zx c a b ni)) (AsSxs-zx c a b ne)
AsSxs-gen (hf-xx a b c d ni ni′) with a ≟ b | c ≟ d
... | yes e  | _       = ⊥-elim-irr (ni e)
... | no  _  | yes e   = ⊥-elim-irr (ni′ e)
... | no  ne | no  ne′ = AsSxs-≈ (refl≡ (gen-xx a b c d ni ni′))
                                 (AsSxs-xx a b c d ne ne′)

AsSxs-word : ∀ {w : W} → HFreeʷ w → AsSxs w
AsSxs-word (gen h)   = AsSxs-gen h
AsSxs-word nil       = AsSxs-ε
AsSxs-word (cat p q) = AsSxs-• (AsSxs-word p) (AsSxs-word q)

-- Lemma A.4, the existence half: any word over P with no Hadamard
-- letter is equivalent to one of the form (B).
existence : ∀ {w : W} → HFreeʷ w → Reduced w
existence h = reduced (Reduced.lis r) (Reduced.code r)
                      (trans (AsSxs.law a) (Reduced.law r))
                      (Reduced.norm r)
  where
  a = AsSxs-word h
  r = reduce (AsSxs.ixs a) (AsSxs.ok a)

------------------------------------------------------------------------
-- Corollary A.5
--
-- Two Hadamard-free words with the same signed permutation are
-- equivalent.  `existence` reduces each to a word of the form (B), and
-- `SignedPerm.sound` carries those reductions into signed
-- permutations, since they are derivations of the Hadamard-free
-- fragment; so all that is left of Lemma A.4 is that a word of the
-- form (B) is *determined* by the signed permutation it denotes.
--
-- That is the statement `Unique` below, and it is the one thing still
-- open here.  It is a statement about (B) alone, with no syntax in it:
-- the permutation part is a Lehmer code, and reading the code back off
-- the permutation is the classical inverse — the i-th entry is where
-- the permutation sends N − i once the earlier runs are stripped off —
-- after which the sign part is read off the diagonal.

Unique : Set
Unique = ∀ {l l′ : List (Fin N)} {d d′ : ℕ → ℕ} →
         Normal l d → Normal l′ d′ → sp (NF l d) ≐ sp (NF l′ d′) →
         NF l d ≡ NF l′ d′

module _ (unique : Unique) where

  -- Corollary A.5, at the Hadamard-free fragment; `free⇒full-≈` carries
  -- it into Figure 8.
  cor-A5 : ∀ {u v : W} → HFreeʷ u → HFreeʷ v → sp u ≐ sp v → u ≈ v
  cor-A5 hu hv e =
    trans (Reduced.law ru)
          (trans (refl≡ (unique (Reduced.norm ru) (Reduced.norm rv) same))
                 (sym (Reduced.law rv)))
    where
    ru = existence hu
    rv = existence hv

    same : sp (NF (Reduced.lis ru) (Reduced.code ru))
         ≐ sp (NF (Reduced.lis rv) (Reduced.code rv))
    same = ≐-trans (≐-sym (sound (Reduced.law ru)))
                   (≐-trans e (sound (Reduced.law rv)))
