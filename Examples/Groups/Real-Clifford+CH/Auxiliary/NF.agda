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

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_ ; toℕ-injective)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (zero ; suc ; _<_ ; _≤_ ; _∸_ ; _<?_) renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (yes ; no)
open import Data.Nat.Properties using (≤-<-trans ; <⇒≤ ; ≮⇒≥ ; ≤∧≢⇒<)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m
  using (zz-comm ; zz-split ; zz² ; DE-ZZ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (o₁)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zxℕ)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

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
    incr   : Incr 0 l
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
               0 < toℕ x → 0 < toℕ y → Incr 0 l → Incr 0 (toggle x (toggle y l))
toggle²-Incr x y l 0<x 0<y i = toggle-Incr x _ 0<x (toggle-Incr y l 0<y i)

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
                   0 < toℕ x → 0 < toℕ y → Normal l d →
                   Normal (toggle x (toggle y l)) d
absorb-zz-Normal x y l d 0<x 0<y nm =
  normal (toggle²-Incr x y l 0<x 0<y (Normal.incr nm))
         (toggle²-Even x y l (Normal.even nm))
         (Normal.lehmer nm)
