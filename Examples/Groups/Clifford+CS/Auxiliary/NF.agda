------------------------------------------------------------------------
-- Presentations of groups
--
-- The normal form of the K-free fragment
--
-- Any word over P′ with no K letter is equivalent to
--
--     atoms l • ∏_{i=1}^{N−1} ( ∏_{j=dᵢ}^{N−i−1} ((−1)[j] X[j,j+1]) )
--
-- with l a strictly increasing list of (index , phase) entries, the
-- index 0 excluded and the phases non-zero (`Atoms`), and dᵢ ≤ N − i a
-- Lehmer code, both products in increasing order and an empty one
-- being ε.  The lists count 4^(N−1) and the codes N!, the order of the
-- det-1 phased permutations (scratchpad/tNFcs.py), so once uniqueness
-- is in, two K-free words with the same phased permutation are equal.
--
-- After Real-Clifford+CH's Auxiliary.NF, with three simplifications:
-- the sign part needs no pairing and no evenness, an exchange pair is
-- always written in increasing order, and the shrinking induction
-- needs no parity — the lower index always moves up.  A letter lands
-- in the permutation part exactly as there: it commutes past a run
-- starting two or more above it, extends one starting just above it,
-- squares into a phase word against one starting at it, and passes
-- through one starting below it, coming out one lower.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.NF (N′ : ℕ) where

private
  N : ℕ
  N = ℕ.suc N′

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (_≟_ ; toℕ-injective ; toℕ-fromℕ< ; toℕ<n)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Nat
  using (zero ; suc ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<?_ ; _≤?_ ; z≤n ; s≤s)
open import Data.Nat.Properties
  using (≤-<-trans ; <-trans ; ≤-trans ; <-≤-trans ; ≤-refl ; ≤-reflexive
       ; <⇒≤ ; ≮⇒≥ ; ≤∧≢⇒< ; n<1+n ; n≤1+n ; n≮n ; <-cmp ; <-irrefl
       ; suc-injective ; +-suc ; +-identityʳ ; +-monoʳ-< ; m≤n+m ; m∸n+n≡m
       ; m+[n∸m]≡n ; ∸-monoʳ-≤ ; n∸n≡0 ; ≤-antisym)
  renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (_,_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; subst₂)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _^_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment
open import Examples.Groups.Clifford+CS.Auxiliary.Derived N
open import Examples.Groups.Clifford+CS.Auxiliary.Atoms N′
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm N
  using (Ph ; p0 ; p1 ; p2 ; p3 ; _+ᵖ_ ; _≐_ ; sp ; sound ; ≐-sym ; ≐-trans)

private
  W : Set
  W = Word (GenP N)

-- The Fin ordering, spelled on the numbers.
infix 4 _<ᶠ_
_<ᶠ_ : Fin N → Fin N → Set
x <ᶠ y = toℕ x < toℕ y

------------------------------------------------------------------------
-- The letters of the permutation part
--
-- The letter on the consecutive pair (j , j + 1) with its phase on j,
-- indexed by naturals, since the normal form's indices are arithmetic
-- on a symbolic N.

fin : (j : ℕ) → j < N → Fin N
fin j p = fromℕ< p

fin-toℕ : ∀ (j : ℕ) (p : j < N) → toℕ (fin j p) ≡ j
fin-toℕ j p = toℕ-fromℕ< p

fin-irr : ∀ (j : ℕ) (p q : j < N) → fin j p ≡ fin j q
fin-irr j p q = toℕ-injective (Eq.trans (fin-toℕ j p) (Eq.sym (fin-toℕ j q)))

fin-succ : ∀ (j : ℕ) (q : j < N) (p : suc j < N) →
           Succ (fin j q) (fin (suc j) p)
fin-succ j q p = Eq.trans (fin-toℕ (suc j) p) (Eq.cong suc (Eq.sym (fin-toℕ j q)))

fin≢ : ∀ {j k : ℕ} (q : j < N) (p : k < N) → j ≢ k → fin j q ≢ fin k p
fin≢ {j} {k} q p ne e =
  ne (Eq.trans (Eq.sym (fin-toℕ j q)) (Eq.trans (Eq.cong toℕ e) (fin-toℕ k p)))

fin<⇒≢ : ∀ {a b : Fin N} → toℕ a < toℕ b → a ≢ b
fin<⇒≢ {a} lt e =
  n≮n (toℕ a) (Eq.subst (toℕ a <_) (Eq.cong toℕ (Eq.sym e)) lt)

n≢sn : ∀ (j : ℕ) → j ≢ suc j
n≢sn zero    ()
n≢sn (suc j) e = n≢sn j (suc-injective e)

j<sj<N : ∀ {j : ℕ} → suc j < N → j < N
j<sj<N p = <-trans (n<1+n _) p

  -- Two letters with the same indices are the same letter.
xw-cong : ∀ {c c′ x x′ y y′ : Fin N} .{q : x <ᶠ y} .{q′ : x′ <ᶠ y′} →
          c ≡ c′ → x ≡ x′ → y ≡ y′ → xw c x y q ≡ xw c′ x′ y′ q′
xw-cong Eq.refl Eq.refl Eq.refl = Eq.refl

sx : ℕ → W
sx j with suc j <? N
... | yes p = sxF (fin j (j<sj<N p)) (fin (suc j) p) (fin-succ j (j<sj<N p) p)
... | no  _ = ε

-- The wrapper on an index known to be in range.
sx-letter : ∀ (j : ℕ) (p : suc j < N) →
          sx j ≡ sxF (fin j (j<sj<N p)) (fin (suc j) p) (fin-succ j (j<sj<N p) p)
sx-letter j p with suc j <? N
... | yes q = xw-cong (fin-irr j (j<sj<N q) (j<sj<N p))
                    (fin-irr j (j<sj<N q) (j<sj<N p)) (fin-irr (suc j) q p)
... | no ¬q = ⊥-elim (¬q p)

------------------------------------------------------------------------
-- The relations of the letters

-- A square is a phase word: the two pp-letters of px-sq.
sx-square : ∀ (j : ℕ) (p : suc j < N) →
            sx j • sx j ≈ pw (fin (suc j) p) (fin j (j<sj<N p))
                          • pw (fin (suc j) p) (fin j (j<sj<N p)) ^ 1
sx-square j p = begin
  sx j • sx j
    ≈⟨ refl≡ (Eq.cong₂ _•_ (sx-letter j p) (sx-letter j p)) ⟩
  sxF a a′ s • sxF a a′ s
    ≈⟨ sym (axiom (px-sq a a′ s)) ⟩
  pw a a′ • pw a a′
    ≈⟨ pp-swap² a′ a ⟩
  pw a′ a • pw a′ a ∎
  where
  a  = fin j (j<sj<N p)
  a′ = fin (suc j) p
  s  = fin-succ j (j<sj<N p) p

-- Letters on pairs two apart commute.
sx-far : ∀ (i j : ℕ) (pi : suc i < N) (pj : suc j < N) →
         suc i < j → sx j • sx i ≈ sx i • sx j
sx-far i j pi pj lt = begin
  sx j • sx i
    ≈⟨ refl≡ (Eq.cong₂ _•_ (sx-letter j pj) (sx-letter i pi)) ⟩
  sxF b b′ s′ • sxF a a′ s
    ≈⟨ sym (axiom (px-comm a a′ b b′ s s′ a′<b)) ⟩
  sxF a a′ s • sxF b b′ s′
    ≈⟨ refl≡ (Eq.cong₂ _•_ (Eq.sym (sx-letter i pi)) (Eq.sym (sx-letter j pj))) ⟩
  sx i • sx j ∎
  where
  a  = fin i (j<sj<N pi)
  a′ = fin (suc i) pi
  b  = fin j (j<sj<N pj)
  b′ = fin (suc j) pj
  s  = fin-succ i (j<sj<N pi) pi
  s′ = fin-succ j (j<sj<N pj) pj

  a′<b : a′ <ᶠ b
  a′<b = subst₂ _<_ (Eq.sym (fin-toℕ (suc i) pi)) (Eq.sym (fin-toℕ j (j<sj<N pj))) lt

-- Neighbouring letters braid.
sx-braid : ∀ (j : ℕ) (p : suc j < N) (r : suc (suc j) < N) →
           sx j • sx (suc j) • sx j ≈ sx (suc j) • sx j • sx (suc j)
sx-braid j p r = begin
  sx j • sx (suc j) • sx j
    ≈⟨ refl≡ (Eq.cong₂ _•_ (sx-letter j p)
                (Eq.cong₂ _•_ sl′ (sx-letter j p))) ⟩
  sxF a a′ s • sxF a′ a″ s′ • sxF a a′ s
    ≈⟨ axiom (px-braid a a′ a″ s s′) ⟩
  sxF a′ a″ s′ • sxF a a′ s • sxF a′ a″ s′
    ≈⟨ refl≡ (Eq.cong₂ _•_ (Eq.sym sl′)
                (Eq.cong₂ _•_ (Eq.sym (sx-letter j p)) (Eq.sym sl′))) ⟩
  sx (suc j) • sx j • sx (suc j) ∎
  where
  a   = fin j (j<sj<N p)
  a′  = fin (suc j) p
  a″  = fin (suc (suc j)) r
  s   = fin-succ j (j<sj<N p) p
  s′₀ = fin-succ (suc j) (j<sj<N r) r

  -- The middle letter read with the bound of the outer one.
  s′ : Succ a′ a″
  s′ = Eq.trans (fin-toℕ (suc (suc j)) r) (Eq.cong suc (Eq.sym (fin-toℕ (suc j) p)))

  sl′ : sx (suc j) ≡ sxF a′ a″ s′
  sl′ = Eq.trans (sx-letter (suc j) r)
                 (xw-cong (fin-irr (suc j) (j<sj<N r) p)
                          (fin-irr (suc j) (j<sj<N r) p) Eq.refl)

------------------------------------------------------------------------
-- Runs and the permutation part

runFrom : ℕ → ℕ → W
runFrom d zero    = ε
runFrom d (suc k) = sx d • runFrom (suc d) k

runAt : ℕ → ℕ → W
runAt i dᵢ = runFrom dᵢ (N ∸ i ∸ dᵢ)

permFrom : ℕ → ℕ → (ℕ → ℕ) → W
permFrom i zero    d = ε
permFrom i (suc k) d = runAt i (d i) • permFrom (suc i) k d

permPart : (ℕ → ℕ) → W
permPart = permFrom 1 (N ∸ 1)

Lehmer : (ℕ → ℕ) → Set
Lehmer d = ∀ i → d i ≤ N ∸ i

------------------------------------------------------------------------
-- The normal form

NF : PhList → (ℕ → ℕ) → W
NF l d = atoms l • permPart d

record Normal (l : PhList) (d : ℕ → ℕ) : Set where
  constructor normal
  field
    incr   : Incr 0 l
    nz     : NZL l
    lehmer : Lehmer d

------------------------------------------------------------------------
-- How a letter meets a run

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
    ≈⟨ front _ (sym (sx-far j d jN (bounds-hd b) lt)) ⟩
  (sx d • sx j) • runFrom (suc d) k
    ≈⟨ assoc ⟩
  sx d • (sx j • runFrom (suc d) k)
    ≈⟨ back _ (sx-below j (suc d) k jN (bounds-tl b) (<-trans lt (n<1+n d))) ⟩
  sx d • (runFrom (suc d) k • sx j)
    ≈⟨ sym assoc ⟩
  (sx d • runFrom (suc d) k) • sx j ∎

-- A letter just below a run extends it, definitionally.
sx-extend : ∀ (d k : ℕ) → sx d • runFrom (suc d) k ≡ runFrom d (suc k)
sx-extend d k = Eq.refl

-- A letter inside a run passes through it and comes out one lower.
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
    ≈⟨ front _ (sym (sx-braid d sdN jN)) ⟩
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
sx-through (suc g) d zero jN b lt =
  ⊥-elim (n≮n (g + d)
    (≤-trans (≤-trans (n≤1+n (suc (g + d))) (n≤1+n (suc (suc (g + d)))))
             (≤-trans (Eq.subst (suc (suc (suc (g + d))) ≤_) (+-identityʳ d) lt)
                      (m≤n+m d g))))
sx-through (suc g) d (suc k) jN b lt = begin
  sx (suc (suc (g + d))) • (sx d • R)
    ≈⟨ sym assoc ⟩
  (sx (suc (suc (g + d))) • sx d) • R
    ≈⟨ front _ (sx-far d (suc (suc (g + d))) (bounds-hd b) jN
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

private
  pred≤ : ∀ {a b : ℕ} → suc a ≤ suc b → a ≤ b
  pred≤ (s≤s le) = le

  ∸suc′ : ∀ (M j : ℕ) → suc j ≤ M → M ∸ j ≡ suc (M ∸ suc j)
  ∸suc′ (suc M) zero    le       = Eq.refl
  ∸suc′ (suc M) (suc j) (s≤s le) = ∸suc′ M j le

  ∸-shift : ∀ (P i : ℕ) → P ∸ suc i ≡ (P ∸ i) ∸ 1
  ∸-shift zero    zero    = Eq.refl
  ∸-shift zero    (suc i) = Eq.refl
  ∸-shift (suc P) zero    = Eq.refl
  ∸-shift (suc P) (suc i) = ∸-shift P i

  suc∸1 : ∀ (j : ℕ) → 0 < j → suc (j ∸ 1) ≡ j
  suc∸1 (suc j) _ = Eq.refl

  0<N : 0 < N
  0<N = s≤s z≤n

  bump : ∀ (P : ℕ) → 0 < P → ∀ (x : ℕ) → x < P ∸ 1 → suc x < P
  bump (suc P) _ x lt = s≤s lt

shift-Ni : ∀ (i k : ℕ) → N ∸ i ≡ suc k → N ∸ suc i ≡ k
shift-Ni i k Ni = Eq.trans (∸-shift N i) (Eq.cong (_∸ 1) Ni)

runAt≡ : ∀ (i v : ℕ) {k : ℕ} → N ∸ i ≡ k → runAt i v ≡ runFrom v (k ∸ v)
runAt≡ i v Ni = Eq.cong (λ z → runFrom v (z ∸ v)) Ni

run-bounds : ∀ (i k v : ℕ) → 1 ≤ i → N ∸ i ≡ k → v ≤ k → Bounds v (k ∸ v)
run-bounds i k v 1i Ni vk t lt = bump N 0<N (v + t) v+t<N-1
  where
  v+t<k : v + t < k
  v+t<k = Eq.subst (v + t <_) (m+[n∸m]≡n vk) (+-monoʳ-< v lt)

  k≤N-1 : k ≤ N ∸ 1
  k≤N-1 = ≤-trans (≤-reflexive (Eq.sym Ni)) (∸-monoʳ-≤ N 1i)

  v+t<N-1 : v + t < N ∸ 1
  v+t<N-1 = <-≤-trans v+t<k k≤N-1

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
  go : Dec (t ≡ i) → upd d i v t ≤ N ∸ t
  go (yes Eq.refl) = Eq.subst (_≤ N ∸ t) (Eq.sym (upd-at d t v)) le
  go (no  ne)      = Eq.subst (_≤ N ∸ t) (Eq.sym (upd-off d i v t ne)) (L t)

permFrom-ext : ∀ (i k : ℕ) (d d′ : ℕ → ℕ) → (∀ t → i ≤ t → d t ≡ d′ t) →
               permFrom i k d ≡ permFrom i k d′
permFrom-ext i zero    d d′ ag = Eq.refl
permFrom-ext i (suc k) d d′ ag =
  Eq.cong₂ _•_ (Eq.cong (runAt i) (ag i ≤-refl))
               (permFrom-ext (suc i) k d d′ (λ t le → ag t (≤-trans (n≤1+n i) le)))

------------------------------------------------------------------------
-- A phase word passes a run
--
-- A letter carries any phase pair to a phase pair (`conj-any`), so a
-- pair, or any power of one, moves left through a run and comes out a
-- pair again.

record PastP (w : W) (x y : Fin N) : Set where
  constructor pastP
  field
    ox oy : Fin N
    law   : w • pw x y ≈ pw ox oy • w

run-pastP : ∀ (d k : ℕ) → Bounds d k → ∀ (x y : Fin N) → PastP (runFrom d k) x y
run-pastP d zero    b x y = pastP x y (trans left-unit (sym right-unit))
run-pastP d (suc k) b x y = pastP (Conj.cx cj) (Conj.cy cj) eq
  where
  R   = runFrom (suc d) k
  p   = run-pastP (suc d) k (bounds-tl b) x y
  sdN = bounds-hd b
  a   = fin d (j<sj<N sdN)
  a′  = fin (suc d) sdN
  s   = fin-succ d (j<sj<N sdN) sdN
  cj  = conj-any a a′ s (PastP.ox p) (PastP.oy p)

  law′ : sx d • pw (PastP.ox p) (PastP.oy p) ≈ pw (Conj.cx cj) (Conj.cy cj) • sx d
  law′ = begin
    sx d • pw (PastP.ox p) (PastP.oy p)
      ≈⟨ front _ (refl≡ (sx-letter d sdN)) ⟩
    sxF a a′ s • pw (PastP.ox p) (PastP.oy p)
      ≈⟨ Conj.law cj ⟩
    pw (Conj.cx cj) (Conj.cy cj) • sxF a a′ s
      ≈⟨ back _ (refl≡ (Eq.sym (sx-letter d sdN))) ⟩
    pw (Conj.cx cj) (Conj.cy cj) • sx d ∎

  eq : (sx d • R) • pw x y ≈ pw (Conj.cx cj) (Conj.cy cj) • (sx d • R)
  eq = begin
    (sx d • R) • pw x y                        ≈⟨ assoc ⟩
    sx d • (R • pw x y)                        ≈⟨ back _ (PastP.law p) ⟩
    sx d • (pw (PastP.ox p) (PastP.oy p) • R)  ≈⟨ sym assoc ⟩
    (sx d • pw (PastP.ox p) (PastP.oy p)) • R  ≈⟨ front _ law′ ⟩
    (pw (Conj.cx cj) (Conj.cy cj) • sx d) • R  ≈⟨ assoc ⟩
    pw (Conj.cx cj) (Conj.cy cj) • (sx d • R) ∎

------------------------------------------------------------------------
-- The phase word a letter leaves behind
--
-- Pushing one letter into the permutation part emits at most one
-- squared pair — `px-sq`, when the letter lands on the start of a run.

data Emis : Set where
  none : Emis
  sq   : Fin N → Fin N → Emis

wrd : Emis → W
wrd none     = ε
wrd (sq x y) = pw x y • pw x y ^ 1

app : Emis → PhList → PhList
app none     l = l
app (sq x y) l = mergePow x y p2 l

app-Incr : ∀ (s : Emis) (l : PhList) → Incr 0 l → Incr 0 (app s l)
app-Incr none     l i = i
app-Incr (sq x y) l i = mergePow-Incr x y p2 l i

app-NZL : ∀ (s : Emis) (l : PhList) → NZL l → NZL (app s l)
app-NZL none     l z = z
app-NZL (sq x y) l z = mergePow-NZL x y p2 l z

app-atoms : ∀ (s : Emis) (l : PhList) → wrd s • atoms l ≈ atoms (app s l)
app-atoms none     l = left-unit
app-atoms (sq x y) l = begin
  (pw x y • pw x y ^ 1) • atoms l   ≈⟨ front _ (sym (^-+ (pw x y) 1 1)) ⟩
  pw x y ^ 2 • atoms l              ≈⟨ mergePow-law x y p2 l ⟩
  atoms (mergePow x y p2 l) ∎

-- A run lets any such phase word through.
record PastS (w : W) (s : Emis) : Set where
  constructor pastS
  field
    out : Emis
    law : w • wrd s ≈ wrd out • w

run-past : ∀ (d k : ℕ) → Bounds d k → (s : Emis) → PastS (runFrom d k) s
run-past d k b none       = pastS none (trans right-unit (sym left-unit))
run-past d k b (sq x y)   = pastS (sq (PastP.ox p) (PastP.oy p)) law′
  where
  p = run-pastP d k b x y
  R = runFrom d k

  law′ : R • (pw x y • pw x y ^ 1) ≈ (pw (PastP.ox p) (PastP.oy p)
                                      • pw (PastP.ox p) (PastP.oy p) ^ 1) • R
  law′ = begin
    R • (pw x y • pw x y ^ 1)
      ≈⟨ back _ (sym (^-+ (pw x y) 1 1)) ⟩
    R • pw x y ^ 2
      ≈⟨ pass-pow (PastP.law p) 2 ⟩
    pw (PastP.ox p) (PastP.oy p) ^ 2 • R
      ≈⟨ front _ (^-+ (pw (PastP.ox p) (PastP.oy p)) 1 1) ⟩
    (pw (PastP.ox p) (PastP.oy p) • pw (PastP.ox p) (PastP.oy p) ^ 1) • R ∎

past-mid : ∀ (w : W) (s : Emis) (ps : PastS w s) (P : W) →
           w • (wrd s • P) ≈ wrd (PastS.out ps) • (w • P)
past-mid w s ps P = begin
  w • (wrd s • P)               ≈⟨ sym assoc ⟩
  (w • wrd s) • P               ≈⟨ front _ (PastS.law ps) ⟩
  (wrd (PastS.out ps) • w) • P  ≈⟨ assoc ⟩
  wrd (PastS.out ps) • (w • P) ∎

------------------------------------------------------------------------
-- Pushing a letter into the permutation part

record Absorbed (i k j : ℕ) (d : ℕ → ℕ) : Set where
  constructor absorbed
  field
    emis   : Emis
    code   : ℕ → ℕ
    law    : sx j • permFrom i k d ≈ wrd emis • permFrom i k code
    lehmer : Lehmer code
    below  : ∀ t → t < i → code t ≡ d t

private
  off : ∀ {t i : ℕ} → t < i → t ≢ i
  off {t} {i} lt e = n≮n i (Eq.subst (_< i) e lt)

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
  s   = Absorbed.emis ih
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
-- At it: the square is a phase word, and the run loses its first letter.
absorb-fuel (suc f) i (suc k) j d (s≤s fk) 1i Ni sj L | tri> _ _ gt | yes e =
  absorbed (sq (fin (suc j) sjN) (fin j (j<sj<N sjN))) c eq lem bel
  where
  v   = d i
  P   = permFrom (suc i) k d
  c   = upd d i (suc j)
  P′  = permFrom (suc i) k c
  L′  = suc k ∸ suc j
  sjN = idx-bound i (suc k) j 1i Ni sj

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

  sqw : sx j • runFrom j (suc L′)
        ≈ (pw (fin (suc j) sjN) (fin j (j<sj<N sjN))
           • pw (fin (suc j) sjN) (fin j (j<sj<N sjN)) ^ 1) • runFrom (suc j) L′
  sqw = begin
    sx j • (sx j • runFrom (suc j) L′)
      ≈⟨ sym assoc ⟩
    (sx j • sx j) • runFrom (suc j) L′
      ≈⟨ front _ (sx-square j sjN) ⟩
    (pw (fin (suc j) sjN) (fin j (j<sj<N sjN))
     • pw (fin (suc j) sjN) (fin j (j<sj<N sjN)) ^ 1) • runFrom (suc j) L′ ∎

  eq : sx j • permFrom i (suc k) d ≈
       wrd (sq (fin (suc j) sjN) (fin j (j<sj<N sjN))) • permFrom i (suc k) c
  eq = begin
    sx j • (runAt i v • P)
      ≈⟨ sym assoc ⟩
    (sx j • runAt i v) • P
      ≈⟨ front _ (refl≡ (Eq.cong (sx j •_) rA)) ⟩
    (sx j • runFrom j (suc L′)) • P
      ≈⟨ front _ sqw ⟩
    ((pw (fin (suc j) sjN) (fin j (j<sj<N sjN))
      • pw (fin (suc j) sjN) (fin j (j<sj<N sjN)) ^ 1) • runFrom (suc j) L′) • P
      ≈⟨ assoc ⟩
    (pw (fin (suc j) sjN) (fin j (j<sj<N sjN))
     • pw (fin (suc j) sjN) (fin j (j<sj<N sjN)) ^ 1) • (runFrom (suc j) L′ • P)
      ≈⟨ back _ (refl≡ (Eq.cong₂ _•_ run≡ P≡)) ⟩
    wrd (sq (fin (suc j) sjN) (fin j (j<sj<N sjN))) • (runAt i (c i) • P′) ∎
    where
    run≡ : runFrom (suc j) L′ ≡ runAt i (c i)
    run≡ = Eq.sym (Eq.trans (Eq.cong (runAt i) (upd-at d i (suc j)))
                            (runAt≡ i (suc j) Ni))

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
  s   = Absorbed.emis ih
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

absorb-perm : ∀ (j : ℕ) (d : ℕ → ℕ) → suc j ≤ N ∸ 1 → Lehmer d →
              Absorbed 1 (N ∸ 1) j d
absorb-perm j d sj L = absorb-fuel (N ∸ 1) 1 (N ∸ 1) j d ≤-refl ≤-refl Eq.refl sj L

------------------------------------------------------------------------
-- A letter passes the phase part
--
-- Per entry: the letter carries the atom's pair to a pair, the power
-- going along, and the image merges into the outgoing list.

record PastSign (j : ℕ) (l : PhList) : Set where
  constructor pastSign
  field
    out  : PhList
    law  : sx j • atoms l ≈ atoms out • sx j
    incr : Incr 0 out
    nz   : NZL out

sx-past : ∀ (j : ℕ) (sjN : suc j < N) (l : PhList) →
          Incr 0 l → NZL l → PastSign j l
sx-past j sjN [] i₀ nil = pastSign [] (trans right-unit (sym left-unit)) nil nil
sx-past j sjN ((x , k) ∷ l) (cons _ i) (cons zk z) =
  pastSign (mergePow (Conj.cx cj) (Conj.cy cj) k out)
           law′
           (mergePow-Incr (Conj.cx cj) (Conj.cy cj) k out (PastSign.incr ih))
           (mergePow-NZL (Conj.cx cj) (Conj.cy cj) k out (PastSign.nz ih))
  where
  ih  = sx-past j sjN l (Incr-mono z≤n i) z
  out = PastSign.out ih
  a   = fin j (j<sj<N sjN)
  a′  = fin (suc j) sjN
  s   = fin-succ j (j<sj<N sjN) sjN
  cj  = conj-any a a′ s x z0

  step : sx j • aw x k ≈ pw (Conj.cx cj) (Conj.cy cj) ^ pn k • sx j
  step = begin
    sx j • aw x k
      ≈⟨ front _ (refl≡ (sx-letter j sjN)) ⟩
    sxF a a′ s • pw x z0 ^ pn k
      ≈⟨ pass-pow (Conj.law cj) (pn k) ⟩
    pw (Conj.cx cj) (Conj.cy cj) ^ pn k • sxF a a′ s
      ≈⟨ back _ (refl≡ (Eq.sym (sx-letter j sjN))) ⟩
    pw (Conj.cx cj) (Conj.cy cj) ^ pn k • sx j ∎

  law′ : sx j • (aw x k • atoms l)
         ≈ atoms (mergePow (Conj.cx cj) (Conj.cy cj) k out) • sx j
  law′ = begin
    sx j • (aw x k • atoms l)
      ≈⟨ sym assoc ⟩
    (sx j • aw x k) • atoms l
      ≈⟨ front _ step ⟩
    (pw (Conj.cx cj) (Conj.cy cj) ^ pn k • sx j) • atoms l
      ≈⟨ assoc ⟩
    pw (Conj.cx cj) (Conj.cy cj) ^ pn k • (sx j • atoms l)
      ≈⟨ back _ (PastSign.law ih) ⟩
    pw (Conj.cx cj) (Conj.cy cj) ^ pn k • (atoms out • sx j)
      ≈⟨ sym assoc ⟩
    (pw (Conj.cx cj) (Conj.cy cj) ^ pn k • atoms out) • sx j
      ≈⟨ front _ (mergePow-law (Conj.cx cj) (Conj.cy cj) k out) ⟩
    atoms (mergePow (Conj.cx cj) (Conj.cy cj) k out) • sx j ∎

-- An emitted phase word moves out past the phase part.
atoms-emis : ∀ (l : PhList) (s : Emis) → atoms l • wrd s ≈ wrd s • atoms l
atoms-emis l none       = trans right-unit (sym left-unit)
atoms-emis l (sq x y)   = begin
  atoms l • (pw x y • pw x y ^ 1)   ≈⟨ back _ (sym (^-+ (pw x y) 1 1)) ⟩
  atoms l • pw x y ^ 2              ≈⟨ atoms-pw-pow l x y 2 ⟩
  pw x y ^ 2 • atoms l              ≈⟨ front _ (^-+ (pw x y) 1 1) ⟩
  (pw x y • pw x y ^ 1) • atoms l ∎

------------------------------------------------------------------------
-- One letter of the permutation part, absorbed

record Absorb (j : ℕ) (l : PhList) (d : ℕ → ℕ) : Set where
  constructor absorb
  field
    lis  : PhList
    code : ℕ → ℕ
    law  : sx j • NF l d ≈ NF lis code
    norm : Normal lis code

absorb-sx : ∀ (j : ℕ) (l : PhList) (d : ℕ → ℕ) →
            suc j ≤ N ∸ 1 → Normal l d → Absorb j l d
absorb-sx j l d sj nm = absorb (app s l₁) (Absorbed.code ap) law′ norm′
  where
  sjN = idx-bound 1 (N ∸ 1) j ≤-refl Eq.refl sj
  ps  = sx-past j sjN l (Normal.incr nm) (Normal.nz nm)
  l₁  = PastSign.out ps
  ap  = absorb-perm j d sj (Normal.lehmer nm)
  s   = Absorbed.emis ap
  d′  = Absorbed.code ap

  norm′ : Normal (app s l₁) d′
  norm′ = normal (app-Incr s l₁ (PastSign.incr ps))
                 (app-NZL s l₁ (PastSign.nz ps))
                 (Absorbed.lehmer ap)

  law′ : sx j • (atoms l • permPart d) ≈ atoms (app s l₁) • permPart d′
  law′ = begin
    sx j • (atoms l • permPart d)      ≈⟨ sym assoc ⟩
    (sx j • atoms l) • permPart d      ≈⟨ front _ (PastSign.law ps) ⟩
    (atoms l₁ • sx j) • permPart d     ≈⟨ assoc ⟩
    atoms l₁ • (sx j • permPart d)     ≈⟨ back _ (Absorbed.law ap) ⟩
    atoms l₁ • (wrd s • permPart d′)   ≈⟨ sym assoc ⟩
    (atoms l₁ • wrd s) • permPart d′   ≈⟨ front _ (atoms-emis l₁ s) ⟩
    (wrd s • atoms l₁) • permPart d′   ≈⟨ front _ (app-atoms s l₁) ⟩
    atoms (app s l₁) • permPart d′ ∎

-- A phase pair, absorbed: it merges into the phase part directly, the
-- permutation part untouched.
record Absorbᵖ (x y : Fin N) (l : PhList) (d : ℕ → ℕ) : Set where
  constructor absorbᵖ
  field
    lis  : PhList
    law  : pw x y • NF l d ≈ NF lis d
    norm : Normal lis d

absorb-pp : ∀ (x y : Fin N) (l : PhList) (d : ℕ → ℕ) →
            Normal l d → Absorbᵖ x y l d
absorb-pp x y l d nm = absorbᵖ (mergePow x y p1 l) law′ norm′
  where
  law′ : pw x y • (atoms l • permPart d)
         ≈ atoms (mergePow x y p1 l) • permPart d
  law′ = begin
    pw x y • (atoms l • permPart d)          ≈⟨ sym assoc ⟩
    (pw x y • atoms l) • permPart d          ≈⟨ front _ (mergePow-law x y p1 l) ⟩
    atoms (mergePow x y p1 l) • permPart d ∎

  norm′ : Normal (mergePow x y p1 l) d
  norm′ = normal (mergePow-Incr x y p1 l (Normal.incr nm))
                 (mergePow-NZL x y p1 l (Normal.nz nm))
                 (Normal.lehmer nm)

------------------------------------------------------------------------
-- Existence, for a word of phase pairs and consecutive letters
--
-- The empty word is the normal form with no phases and dᵢ = N − i,
-- and each further token is absorbed on the left.

data Tok : Set where
  tpp : Fin N → Fin N → Tok
  tsx : ℕ → Tok

tokW : Tok → W
tokW (tpp x y) = pw x y
tokW (tsx j)   = sx j

toks : List Tok → W
toks []       = ε
toks (t ∷ ts) = tokW t • toks ts

data OkT : List Tok → Set where
  nil : OkT []
  cpp : ∀ {x y ts} → OkT ts → OkT (tpp x y ∷ ts)
  csx : ∀ {j ts} → suc j ≤ N ∸ 1 → OkT ts → OkT (tsx j ∷ ts)

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
    lis  : PhList
    code : ℕ → ℕ
    law  : w ≈ NF lis code
    norm : Normal lis code

reduce : ∀ (ts : List Tok) → OkT ts → Reduced (toks ts)
reduce []             nil          =
  reduced [] idCode (sym NF-id) (normal nil nil idCode-Lehmer)
reduce (tpp x y ∷ ts) (cpp oks)    =
  reduced (Absorbᵖ.lis ab) (Reduced.code ih)
          (trans (back _ (Reduced.law ih)) (Absorbᵖ.law ab))
          (Absorbᵖ.norm ab)
  where
  ih = reduce ts oks
  ab = absorb-pp x y (Reduced.lis ih) (Reduced.code ih) (Reduced.norm ih)
reduce (tsx j ∷ ts)   (csx ok oks) =
  reduced (Absorb.lis ab) (Absorb.code ab)
          (trans (back _ (Reduced.law ih)) (Absorb.law ab))
          (Absorb.norm ab)
  where
  ih = reduce ts oks
  ab = absorb-sx j (Reduced.lis ih) (Reduced.code ih) ok (Reduced.norm ih)

------------------------------------------------------------------------
-- Every K-free letter is a word of tokens

record AsToks (w : W) : Set where
  constructor asToks
  field
    ixs : List Tok
    ok  : OkT ixs
    law : w ≈ toks ixs

OkT-++ : ∀ {l l′ : List Tok} → OkT l → OkT l′ → OkT (l ++ l′)
OkT-++ nil         o′ = o′
OkT-++ (cpp o)     o′ = cpp (OkT-++ o o′)
OkT-++ (csx b o)   o′ = csx b (OkT-++ o o′)

toks-++ : ∀ (l l′ : List Tok) → toks (l ++ l′) ≈ toks l • toks l′
toks-++ []      l′ = sym left-unit
toks-++ (t ∷ l) l′ = trans (back _ (toks-++ l l′)) (sym assoc)

AsToks-ε : AsToks ε
AsToks-ε = asToks [] nil refl

AsToks-≈ : ∀ {u v : W} → u ≈ v → AsToks v → AsToks u
AsToks-≈ e a = asToks (AsToks.ixs a) (AsToks.ok a) (trans e (AsToks.law a))

AsToks-• : ∀ {u v : W} → AsToks u → AsToks v → AsToks (u • v)
AsToks-• p q =
  asToks (AsToks.ixs p ++ AsToks.ixs q) (OkT-++ (AsToks.ok p) (AsToks.ok q))
         (trans (cong (AsToks.law p) (AsToks.law q))
                (sym (toks-++ (AsToks.ixs p) (AsToks.ixs q))))

-- A phase pair is one token.
AsToks-pp : ∀ (x y : Fin N) → AsToks (pw x y)
AsToks-pp x y = asToks (tpp x y ∷ []) (cpp nil) (sym right-unit)

private
  down : ∀ (P x : ℕ) → x < P → x ≤ P ∸ 1
  down (suc P) x (s≤s le) = le

  ok-ix : ∀ (a a′ : Fin N) → Succ a a′ → suc (toℕ a) ≤ N ∸ 1
  ok-ix a a′ s = down N (suc (toℕ a)) (Eq.subst (_< N) s (toℕ<n a′))

  fin-of-toℕ : ∀ (a : Fin N) (p : toℕ a < N) → fin (toℕ a) p ≡ a
  fin-of-toℕ a p = toℕ-injective (fin-toℕ (toℕ a) p)

  -- The letter on a consecutive pair is the wrapper at its index.
  sx-lit : ∀ (a a′ : Fin N) (s : Succ a a′) → sxF a a′ s ≡ sx (toℕ a)
  sx-lit a a′ s = Eq.sym (Eq.trans (sx-letter (toℕ a) p) step)
    where
    p : suc (toℕ a) < N
    p = Eq.subst (_< N) s (toℕ<n a′)

    step : sxF (fin (toℕ a) (j<sj<N p)) (fin (suc (toℕ a)) p)
               (fin-succ (toℕ a) (j<sj<N p) p)
           ≡ sxF a a′ s
    step = xw-cong (fin-of-toℕ a (j<sj<N p)) (fin-of-toℕ a (j<sj<N p))
                   (toℕ-injective (Eq.trans (fin-toℕ (suc (toℕ a)) p) (Eq.sym s)))

-- The letter with its phase below.
AsToks-sx : ∀ (a a′ : Fin N) (s : Succ a a′) → AsToks (sxF a a′ s)
AsToks-sx a a′ s =
  asToks (tsx (toℕ a) ∷ []) (csx (ok-ix a a′ s) nil)
         (trans (refl≡ (sx-lit a a′ s)) (sym right-unit))

-- And with its phase above: two phase pairs and the letter, px-sign.
AsToks-sx′ : ∀ (a a′ : Fin N) (s : Succ a a′) → AsToks (xw a′ a a′ (s< s))
AsToks-sx′ a a′ s =
  AsToks-≈ (axiom (px-sign a′ a a′ (s< s)))
           (AsToks-• (AsToks-pp a′ a)
                     (AsToks-• (AsToks-pp a′ a) (AsToks-sx a a′ s)))

-- A letter with its phase on the lower index, by the gap induction:
-- the lower index always moves up, px-shrink₁.
private
  0<gap : ∀ {m n : ℕ} → m < n → 0 < n ∸ m
  0<gap {zero}  {suc n} lt       = s≤s z≤n
  0<gap {suc m} {suc n} (s≤s lt) = 0<gap lt

  pred-≤ : ∀ {m n : ℕ} → m ≤ suc n → m ∸ 1 ≤ n
  pred-≤ {zero}  le       = z≤n
  pred-≤ {suc m} (s≤s le) = le

xw-fuel : ∀ (f : ℕ) (a b : Fin N) (lt : a <ᶠ b) → toℕ b ∸ toℕ a ≤ f →
          AsToks (xw a a b lt)
xw-fuel zero a b lt fu =
  ⊥-elim (<-irrefl Eq.refl (≤-<-trans fu (0<gap lt)))
xw-fuel (suc f) a b lt fu with suc (toℕ a) <? toℕ b
... | no ¬p = AsToks-sx a b (≤-antisym (≮⇒≥ ¬p) lt)
... | yes p = AsToks-≈ (axiom (px-shrink₁ a a′ b s a′<b))
                       (AsToks-• (AsToks-sx′ a a′ s)
                                 (AsToks-• (xw-fuel f a′ b a′<b fu′)
                                           (AsToks-sx a a′ s)))
  where
  saN : suc (toℕ a) < N
  saN = <-trans p (toℕ<n b)

  a′ : Fin N
  a′ = fin (suc (toℕ a)) saN

  s : Succ a a′
  s = fin-toℕ (suc (toℕ a)) saN

  a′<b : a′ <ᶠ b
  a′<b = Eq.subst (λ z → suc z ≤ toℕ b) (Eq.sym (fin-toℕ (suc (toℕ a)) saN)) p

  fu′ : toℕ b ∸ toℕ a′ ≤ f
  fu′ = Eq.subst (λ z → toℕ b ∸ z ≤ f) (Eq.sym (fin-toℕ (suc (toℕ a)) saN))
          (Eq.subst (_≤ f) (Eq.sym (∸-shift (toℕ b) (toℕ a))) (pred-≤ fu))

-- Any letter: the phase moves to the lower index first, px-sign.
AsToks-px : ∀ (c a b : Fin N) .(lt : a <ᶠ b) → AsToks (xw c a b lt)
AsToks-px c a b lt =
  AsToks-≈ (axiom (px-sign c a b lt))
           (AsToks-• (AsToks-pp c a)
                     (AsToks-• (AsToks-pp c a)
                               (xw-fuel (toℕ b ∸ toℕ a) a b lt′ ≤-refl)))
  where
  lt′ : a <ᶠ b
  lt′ = recompute (suc (toℕ a) ≤? toℕ b) lt

-- A double exchange: two letters.
AsToks-dx : ∀ (a b c d : Fin N) .(ab : a <ᶠ b) .(cd : c <ᶠ d) →
            AsToks (dw a b c d ab cd)
AsToks-dx a b c d ab cd =
  AsToks-≈ (axiom (dx-split a b c d ab cd))
           (AsToks-• (AsToks-px a a b ab) (AsToks-px b c d cd))

------------------------------------------------------------------------
-- Existence

-- A letter with no K in it, and a word of such letters.
data KFree : GenP N → Set where
  kf-pp : ∀ (a b : Fin N) → KFree (pp a b)
  kf-px : ∀ (c a b : Fin N) .(lt : a <ᶠ b) → KFree (px c a b lt)
  kf-dx : ∀ (a b c d : Fin N) .(ab : a <ᶠ b) .(cd : c <ᶠ d) →
          KFree (dx a b c d ab cd)

data KFreeʷ : W → Set where
  gen : ∀ {g} → KFree g → KFreeʷ [ g ]ʷ
  nil : KFreeʷ ε
  cat : ∀ {u v} → KFreeʷ u → KFreeʷ v → KFreeʷ (u • v)

AsToks-gen : ∀ {g : GenP N} → KFree g → AsToks [ g ]ʷ
AsToks-gen (kf-pp a b)           = AsToks-pp a b
AsToks-gen (kf-px c a b lt)      = AsToks-px c a b lt
AsToks-gen (kf-dx a b c d ab cd) = AsToks-dx a b c d ab cd

AsToks-word : ∀ {w : W} → KFreeʷ w → AsToks w
AsToks-word (gen h)   = AsToks-gen h
AsToks-word nil       = AsToks-ε
AsToks-word (cat p q) = AsToks-• (AsToks-word p) (AsToks-word q)

-- Existence: any word over P′ with no K letter is equivalent to a
-- normal form.
existence : ∀ {w : W} → KFreeʷ w → Reduced w
existence h = reduced (Reduced.lis r) (Reduced.code r)
                      (trans (AsToks.law a) (Reduced.law r))
                      (Reduced.norm r)
  where
  a = AsToks-word h
  r = reduce (AsToks.ixs a) (AsToks.ok a)

------------------------------------------------------------------------
-- The analogue of Corollary A.5, modulo uniqueness
--
-- Two K-free words with the same phased permutation are equivalent,
-- once a normal form is determined by the phased permutation it
-- denotes.  That statement is `Unique`, the one thing still open; it
-- is a statement about the normal form alone, with no syntax in it.

Unique : Set
Unique = ∀ {l l′ : PhList} {d d′ : ℕ → ℕ} →
         Normal l d → Normal l′ d′ → sp (NF l d) ≐ sp (NF l′ d′) →
         NF l d ≡ NF l′ d′

module _ (unique : Unique) where

  cor-A5 : ∀ {u v : W} → KFreeʷ u → KFreeʷ v → sp u ≐ sp v → u ≈ v
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
