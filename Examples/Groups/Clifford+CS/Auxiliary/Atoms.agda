------------------------------------------------------------------------
-- Presentations of groups
--
-- The phase part of the normal form
--
-- A phase vector is kept as a strictly increasing list of (index ,
-- phase) entries with the phases non-zero and the index 0 excluded:
-- the entry (x , k) stands for the atom (pp x 0)^k, so the phase the
-- whole list leaves at the index 0 is the balance, and the det
-- constraint of the phased-permutation group is absorbed there.  The
-- lists count exactly 4^(N−1), the number of phase parts of the
-- normal form (scratchpad/tNFcs.py).
--
-- Adding a phase at an index is one `tog` — insertion, fusion, or
-- deletion when the fused phase vanishes — and a phase pair pw u v,
-- or any power of one, merges by two (`mergePow`), its split through
-- the anchor being the telescope.  This is the analogue of NF's
-- atoms/toggle machinery in Real-Clifford+CH, with ℤ/4 phases for the
-- signs and no evenness condition.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.Atoms (N′ : ℕ) where

private
  N : ℕ
  N = ℕ.suc N′

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; zero)
open import Data.Fin.Properties using (_≟_ ; toℕ-injective)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (suc ; _+_ ; _<_ ; _≤_ ; _<?_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (≤-<-trans ; <⇒≤ ; ≮⇒≥ ; ≤∧≢⇒<)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _^_)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment
open import Examples.Groups.Clifford+CS.Auxiliary.Derived N
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm N
  using (Ph ; p0 ; p1 ; p2 ; p3 ; _+ᵖ_)

private
  W : Set
  W = Word (GenP N)

refl≡ : {w v : W} → w ≡ v → w ≈ v
refl≡ Eq.refl = refl

-- The anchor.
z0 : Fin N
z0 = zero

------------------------------------------------------------------------
-- Phases as exponents

pn : Ph → ℕ
pn p0 = 0
pn p1 = 1
pn p2 = 2
pn p3 = 3

negᵖ : Ph → Ph
negᵖ p0 = p0
negᵖ p1 = p3
negᵖ p2 = p2
negᵖ p3 = p1

------------------------------------------------------------------------
-- The atoms

aw : Fin N → Ph → W
aw x k = pw x z0 ^ pn k

Entry : Set
Entry = Fin N × Ph

PhList : Set
PhList = List Entry

atoms : PhList → W
atoms []            = ε
atoms ((x , k) ∷ l) = aw x k • atoms l

------------------------------------------------------------------------
-- The side conditions

-- Strictly increasing above a bound; the canonical bound is 0, which
-- excludes the anchor.
data Incr : ℕ → PhList → Set where
  nil  : ∀ {lo} → Incr lo []
  cons : ∀ {lo x k l} → lo < toℕ x → Incr (toℕ x) l → Incr lo ((x , k) ∷ l)

Incr-mono : ∀ {lo lo′ l} → lo ≤ lo′ → Incr lo′ l → Incr lo l
Incr-mono le nil         = nil
Incr-mono le (cons lt i) = cons (≤-<-trans le lt) i

-- The phases are non-zero.
data NZ : Ph → Set where
  nz1 : NZ p1
  nz2 : NZ p2
  nz3 : NZ p3

data NZL : PhList → Set where
  nil  : NZL []
  cons : ∀ {x k l} → NZ k → NZL l → NZL ((x , k) ∷ l)

------------------------------------------------------------------------
-- The atom algebra

-- A fifth factor cancels.
pw-mod4 : ∀ (x y : Fin N) (t : ℕ) → pw x y ^ (4 + t) ≈ pw x y ^ t
pw-mod4 x y t = begin
  pw x y ^ (4 + t)           ≈⟨ ^-+ (pw x y) 4 t ⟩
  pw x y ^ 4 • pw x y ^ t    ≈⟨ front _ (axiom (pp-ord x y)) ⟩
  ε • pw x y ^ t             ≈⟨ left-unit ⟩
  pw x y ^ t ∎

-- Two atoms at one index fuse.
aw-fuse : ∀ (x : Fin N) (k j : Ph) → aw x k • aw x j ≈ aw x (k +ᵖ j)
aw-fuse x k j = trans (sym (^-+ (pw x z0) (pn k) (pn j))) (fix k j)
  where
  P = pw x z0

  fix : ∀ (k j : Ph) → P ^ (pn k + pn j) ≈ P ^ pn (k +ᵖ j)
  fix p0 j  = refl
  fix p1 p0 = refl
  fix p1 p1 = refl
  fix p1 p2 = refl
  fix p1 p3 = pw-mod4 x z0 0
  fix p2 p0 = refl
  fix p2 p1 = refl
  fix p2 p2 = pw-mod4 x z0 0
  fix p2 p3 = pw-mod4 x z0 1
  fix p3 p0 = refl
  fix p3 p1 = pw-mod4 x z0 0
  fix p3 p2 = pw-mod4 x z0 1
  fix p3 p3 = pw-mod4 x z0 2

-- Atoms commute, with one another and with any phase pair.
aw-pw : ∀ (x : Fin N) (k : Ph) (u v : Fin N) →
        aw x k • pw u v ≈ pw u v • aw x k
aw-pw x k u v = go
  where
  base : pw x z0 • pw u v ≈ pw u v • pw x z0
  base = axiom (pp-comm x z0 u v)

  go : pw x z0 ^ pn k • pw u v ≈ pw u v • pw x z0 ^ pn k
  go = trans (comm⇒pow-comm (pn k) 1 base) refl

aw-comm : ∀ (x : Fin N) (k : Ph) (y : Fin N) (j : Ph) →
          aw x k • aw y j ≈ aw y j • aw x k
aw-comm x k y j = comm⇒pow-comm (pn k) (pn j) (axiom (pp-comm x z0 y z0))

-- The atom at the anchor is nothing.
aw-z0 : ∀ (k : Ph) → aw z0 k ≈ ε
aw-z0 k = trans (^-cong (pw z0 z0) ε (pn k) (axiom (pp-id z0))) (ε^k=ε (pn k))

------------------------------------------------------------------------
-- A phase pair, split through the anchor

-- The reverse cubed is the pair.
pp-rev³ : ∀ (x y : Fin N) → pw x y ≈ pw y x ^ 3
pp-rev³ x y = begin
  pw x y                                       ≈⟨ sym right-unit ⟩
  pw x y • ε                                   ≈⟨ back _ (sym (axiom (pp-ord y x))) ⟩
  pw x y • (pw y x • (pw y x • (pw y x • pw y x)))
    ≈⟨ cancelˡ⁻ (pw y x • (pw y x • pw y x)) (pp-inv x y) ⟩
  pw y x • (pw y x • pw y x) ∎

-- A power of a pair is two atom powers.
split-pow : ∀ (u v : Fin N) (k : Ph) →
            pw u v ^ pn k ≈ aw u k • aw v (negᵖ k)
split-pow u v k = begin
  pw u v ^ pn k
    ≈⟨ ^-cong (pw u v) (pw u z0 • pw z0 v) (pn k) (sym (axiom (pp-tele u z0 v))) ⟩
  (pw u z0 • pw z0 v) ^ pn k
    ≈⟨ ^-• (pw u z0) (pw z0 v) (pn k) (axiom (pp-comm u z0 z0 v)) ⟩
  pw u z0 ^ pn k • pw z0 v ^ pn k
    ≈⟨ back _ lower ⟩
  aw u k • aw v (negᵖ k) ∎
  where
  V = pw v z0

  threes : ∀ (k : Ph) → V ^ (pn k Data.Nat.* 3) ≈ V ^ pn (negᵖ k)
  threes p0 = refl
  threes p1 = refl
  threes p2 = pw-mod4 v z0 2
  threes p3 = trans (pw-mod4 v z0 5) (pw-mod4 v z0 1)

  lower : pw z0 v ^ pn k ≈ aw v (negᵖ k)
  lower = begin
    pw z0 v ^ pn k      ≈⟨ ^-cong (pw z0 v) (V ^ 3) (pn k) (pp-rev³ z0 v) ⟩
    (V ^ 3) ^ pn k      ≈⟨ ^^ V 3 (pn k) ⟩
    V ^ (3 Data.Nat.* pn k)
      ≈⟨ refl≡ (Eq.cong (V ^_) (Data.Nat.Properties.*-comm 3 (pn k))) ⟩
    V ^ (pn k Data.Nat.* 3)
      ≈⟨ threes k ⟩
    V ^ pn (negᵖ k) ∎

------------------------------------------------------------------------
-- Toggling an entry

-- The cons that drops a vanished phase.
consNZ : Fin N → Ph → PhList → PhList
consNZ x p0 l = l
consNZ x p1 l = (x , p1) ∷ l
consNZ x p2 l = (x , p2) ∷ l
consNZ x p3 l = (x , p3) ∷ l

atoms-consNZ : ∀ (x : Fin N) (k : Ph) (l : PhList) →
               atoms (consNZ x k l) ≈ aw x k • atoms l
atoms-consNZ x p0 l = sym left-unit
atoms-consNZ x p1 l = refl
atoms-consNZ x p2 l = refl
atoms-consNZ x p3 l = refl

tog : Fin N → Ph → PhList → PhList
tog x k [] = consNZ x k []
tog x k ((y , j) ∷ l) with toℕ x <? toℕ y
... | yes _ = consNZ x k ((y , j) ∷ l)
... | no  _ with x ≟ y
...         | yes _ = consNZ y (k +ᵖ j) l
...         | no  _ = (y , j) ∷ tog x k l

atoms-tog : ∀ (x : Fin N) (k : Ph) (l : PhList) →
            atoms (tog x k l) ≈ aw x k • atoms l
atoms-tog x k [] = atoms-consNZ x k []
atoms-tog x k ((y , j) ∷ l) with toℕ x <? toℕ y
... | yes _ = atoms-consNZ x k ((y , j) ∷ l)
... | no  _ with x ≟ y
...         | yes Eq.refl = begin
  atoms (consNZ y (k +ᵖ j) l)     ≈⟨ atoms-consNZ y (k +ᵖ j) l ⟩
  aw y (k +ᵖ j) • atoms l         ≈⟨ front _ (sym (aw-fuse y k j)) ⟩
  (aw y k • aw y j) • atoms l     ≈⟨ assoc ⟩
  aw y k • (aw y j • atoms l) ∎
...         | no  _ = begin
  aw y j • atoms (tog x k l)      ≈⟨ back _ (atoms-tog x k l) ⟩
  aw y j • (aw x k • atoms l)     ≈⟨ sym assoc ⟩
  (aw y j • aw x k) • atoms l     ≈⟨ front _ (aw-comm y j x k) ⟩
  (aw x k • aw y j) • atoms l     ≈⟨ assoc ⟩
  aw x k • (aw y j • atoms l) ∎

-- Toggling keeps the side conditions.
private
  ≢toℕ : ∀ {x y : Fin N} → x ≢ y → toℕ x ≢ toℕ y
  ≢toℕ ne e = ne (toℕ-injective e)

consNZ-Incr : ∀ {lo} (x : Fin N) (k : Ph) (l : PhList) →
              lo < toℕ x → Incr (toℕ x) l → Incr lo l → Incr lo (consNZ x k l)
consNZ-Incr x p0 l lt i₀ ilo = ilo
consNZ-Incr x p1 l lt i₀ ilo = cons lt i₀
consNZ-Incr x p2 l lt i₀ ilo = cons lt i₀
consNZ-Incr x p3 l lt i₀ ilo = cons lt i₀

tog-Incr : ∀ {lo} (x : Fin N) (k : Ph) (l : PhList) →
           lo < toℕ x → Incr lo l → Incr lo (tog x k l)
tog-Incr x k [] lt nil = consNZ-Incr x k [] lt nil nil
tog-Incr x k ((y , j) ∷ l) lt (cons lo<y i) with toℕ x <? toℕ y
... | yes x<y = consNZ-Incr x k ((y , j) ∷ l) lt (cons x<y i) (cons lo<y i)
... | no  x≮y with x ≟ y
...           | yes Eq.refl =
  consNZ-Incr y (k +ᵖ j) l lo<y i (Incr-mono (<⇒≤ lo<y) i)
...           | no  x≢y =
  cons lo<y (tog-Incr x k l (≤∧≢⇒< (≮⇒≥ x≮y) (λ e → x≢y (toℕ-injective (Eq.sym e)))) i)

consNZ-NZL : ∀ (x : Fin N) (k : Ph) (l : PhList) → NZL l → NZL (consNZ x k l)
consNZ-NZL x p0 l z = z
consNZ-NZL x p1 l z = cons nz1 z
consNZ-NZL x p2 l z = cons nz2 z
consNZ-NZL x p3 l z = cons nz3 z

tog-NZL : ∀ (x : Fin N) (k : Ph) (l : PhList) → NZL l → NZL (tog x k l)
tog-NZL x k [] nil = consNZ-NZL x k [] nil
tog-NZL x k ((y , j) ∷ l) (cons zj z) with toℕ x <? toℕ y
... | yes _ = consNZ-NZL x k ((y , j) ∷ l) (cons zj z)
... | no  _ with x ≟ y
...         | yes _ = consNZ-NZL y (k +ᵖ j) l z
...         | no  _ = cons zj (tog-NZL x k l z)

------------------------------------------------------------------------
-- Merging a power of a phase pair
--
-- pw u v carries +k at u and −k at v; the anchor absorbs its own
-- share, so an index that is the anchor is simply skipped.

private
  ≢z0⇒0< : ∀ {x : Fin N} → x ≢ z0 → 0 < toℕ x
  ≢z0⇒0< {zero} ne      = ⊥-elim (ne Eq.refl)
  ≢z0⇒0< {Fin.suc x} ne = s≤s z≤n

mergePow : Fin N → Fin N → Ph → PhList → PhList
mergePow u v k l with u ≟ z0 | v ≟ z0
... | yes _ | yes _ = l
... | yes _ | no  _ = tog v (negᵖ k) l
... | no  _ | yes _ = tog u k l
... | no  _ | no  _ = tog u k (tog v (negᵖ k) l)

mergePow-law : ∀ (u v : Fin N) (k : Ph) (l : PhList) →
               pw u v ^ pn k • atoms l ≈ atoms (mergePow u v k l)
mergePow-law u v k l with u ≟ z0 | v ≟ z0
... | yes Eq.refl | yes Eq.refl = begin
  pw z0 z0 ^ pn k • atoms l    ≈⟨ front _ (aw-z0 k) ⟩
  ε • atoms l                  ≈⟨ left-unit ⟩
  atoms l ∎
... | yes Eq.refl | no _ = begin
  pw z0 v ^ pn k • atoms l            ≈⟨ front _ lower ⟩
  aw v (negᵖ k) • atoms l             ≈⟨ sym (atoms-tog v (negᵖ k) l) ⟩
  atoms (tog v (negᵖ k) l) ∎
  where
  lower : pw z0 v ^ pn k ≈ aw v (negᵖ k)
  lower = begin
    pw z0 v ^ pn k            ≈⟨ split-pow z0 v k ⟩
    aw z0 k • aw v (negᵖ k)   ≈⟨ front _ (aw-z0 k) ⟩
    ε • aw v (negᵖ k)         ≈⟨ left-unit ⟩
    aw v (negᵖ k) ∎
... | no _ | yes Eq.refl = begin
  pw u z0 ^ pn k • atoms l     ≈⟨ sym (atoms-tog u k l) ⟩
  atoms (tog u k l) ∎
... | no _ | no _ = begin
  pw u v ^ pn k • atoms l               ≈⟨ front _ (split-pow u v k) ⟩
  (aw u k • aw v (negᵖ k)) • atoms l    ≈⟨ assoc ⟩
  aw u k • (aw v (negᵖ k) • atoms l)    ≈⟨ back _ (sym (atoms-tog v (negᵖ k) l)) ⟩
  aw u k • atoms (tog v (negᵖ k) l)     ≈⟨ sym (atoms-tog u k (tog v (negᵖ k) l)) ⟩
  atoms (tog u k (tog v (negᵖ k) l)) ∎

mergePow-Incr : ∀ (u v : Fin N) (k : Ph) (l : PhList) →
                Incr 0 l → Incr 0 (mergePow u v k l)
mergePow-Incr u v k l i with u ≟ z0 | v ≟ z0
... | yes _  | yes _  = i
... | yes _  | no  nv = tog-Incr v (negᵖ k) l (≢z0⇒0< nv) i
... | no  nu | yes _  = tog-Incr u k l (≢z0⇒0< nu) i
... | no  nu | no  nv =
  tog-Incr u k (tog v (negᵖ k) l) (≢z0⇒0< nu)
           (tog-Incr v (negᵖ k) l (≢z0⇒0< nv) i)

mergePow-NZL : ∀ (u v : Fin N) (k : Ph) (l : PhList) →
               NZL l → NZL (mergePow u v k l)
mergePow-NZL u v k l z with u ≟ z0 | v ≟ z0
... | yes _ | yes _ = z
... | yes _ | no  _ = tog-NZL v (negᵖ k) l z
... | no  _ | yes _ = tog-NZL u k l z
... | no  _ | no  _ = tog-NZL u k (tog v (negᵖ k) l) (tog-NZL v (negᵖ k) l z)

------------------------------------------------------------------------
-- The phase part is central

atoms-pw : ∀ (l : PhList) (u v : Fin N) →
           atoms l • pw u v ≈ pw u v • atoms l
atoms-pw [] u v = trans left-unit (sym right-unit)
atoms-pw ((y , j) ∷ l) u v = begin
  (aw y j • atoms l) • pw u v    ≈⟨ assoc ⟩
  aw y j • (atoms l • pw u v)    ≈⟨ back _ (atoms-pw l u v) ⟩
  aw y j • (pw u v • atoms l)    ≈⟨ sym assoc ⟩
  (aw y j • pw u v) • atoms l    ≈⟨ front _ (aw-pw y j u v) ⟩
  (pw u v • aw y j) • atoms l    ≈⟨ assoc ⟩
  pw u v • (aw y j • atoms l) ∎

atoms-pw-pow : ∀ (l : PhList) (u v : Fin N) (k : ℕ) →
               atoms l • pw u v ^ k ≈ pw u v ^ k • atoms l
atoms-pw-pow l u v k = pass-pow (atoms-pw l u v) k
