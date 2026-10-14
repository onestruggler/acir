------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the normal form of the K-free fragment
--
-- A normal form is determined by the phased permutation it denotes,
-- which is the half that `NF` leaves open as `NF.Unique`, and with it
-- the analogue of Corollary A.5 is unconditional.
--
-- The two parts are read back separately.  The phase part permutes
-- nothing, so the permutation of a normal form is the permutation of
-- its Lehmer code alone; and the code is read off that permutation by
-- the classical inverse — the i-th entry is the index the permutation
-- sends to N − i, because the i-th run sends its first index there and
-- every later run leaves N − i alone.  With the codes equal the
-- permutation parts are the same word, and then the phases agree index
-- by index; away from the anchor the phase of the list at an index is
-- its entry there, so the increasing lists coincide entry by entry.
-- The phase the atoms leave at the anchor carries no information: it
-- is the balance, and it agrees as soon as the rest does.
--
-- After Real-Clifford+CH's Auxiliary.Unique, with ℤ/4 phases for the
-- Boolean signs: `mem` becomes the phase of the list at an index, and
-- the non-zero side condition replaces evenness in telling an entry
-- from no entry.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.Unique (N′ : ℕ) where

private
  N : ℕ
  N = ℕ.suc N′

open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_ ; toℕ-injective ; toℕ<n)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (zero ; suc ; _+_ ; _<_ ; _≤_ ; _∸_ ; _<?_ ; z≤n ; s≤s)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; <-trans ; ≤-<-trans ; <-≤-trans ; <⇒≤ ; <-cmp ; n≮n
       ; n<1+n ; n≤1+n ; ≮⇒≥ ; ≤∧≢⇒<
       ; suc-injective ; +-identityʳ ; +-suc ; m≤m+n ; m+[n∸m]≡n ; ∸-monoʳ-≤
       ; m∸n≤m ; n∸n≡0)
  renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (_,_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _^_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment
  using (_F,_===_ ; pw ; xw ; dw ; Succ ; s<)
open import Examples.Groups.Clifford+CS.Auxiliary.Atoms N′
  using (atoms ; aw ; PhList ; Entry ; Incr ; NZL ; NZ ; nz1 ; nz2 ; nz3
       ; nil ; cons ; Incr-mono ; z0 ; pn ; negᵖ)
open import Examples.Groups.Clifford+CS.Auxiliary.NF N′
  using (NF ; Normal ; normal ; Lehmer ; runFrom ; runAt ; permFrom ; permPart
       ; KFreeʷ ; cor-A5 ; sx ; sx-letter ; fin ; fin-toℕ ; fin-irr ; j<sj<N
       ; runAt≡ ; run-bounds ; shift-Ni ; idx-bound)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm N
  using (Ph ; p0 ; p1 ; p2 ; p3 ; _+ᵖ_ ; +ᵖ-idʳ ; +ᵖ-comm ; +ᵖ-assoc
       ; sp ; spg ; ph ; prm ; _≐_ ; ph≡ ; prm≡ ; δ ; δ-here ; δ-≢ ; phif
       ; swapF ; swapF-a ; swapF-o ; swapF-invol ; swapF-inj)

private
  W : Set
  W = Word (GenP N)

------------------------------------------------------------------------
-- The phase arithmetic the read-back needs

private
  negᵖ-inv : ∀ (x : Ph) → x +ᵖ negᵖ x ≡ p0
  negᵖ-inv p0 = Eq.refl
  negᵖ-inv p1 = Eq.refl
  negᵖ-inv p2 = Eq.refl
  negᵖ-inv p3 = Eq.refl

  +ᵖ-cancelʳ : ∀ (x u v : Ph) → u +ᵖ x ≡ v +ᵖ x → u ≡ v
  +ᵖ-cancelʳ x u v e = Eq.trans (peel u) (Eq.trans mid (Eq.sym (peel v)))
    where
    peel : ∀ u → u ≡ (u +ᵖ x) +ᵖ negᵖ x
    peel u = Eq.sym (Eq.trans (+ᵖ-assoc u x (negᵖ x))
                              (Eq.trans (Eq.cong (u +ᵖ_) (negᵖ-inv x)) (+ᵖ-idʳ u)))

    mid : (u +ᵖ x) +ᵖ negᵖ x ≡ (v +ᵖ x) +ᵖ negᵖ x
    mid = Eq.cong (_+ᵖ negᵖ x) e

  nz≢0 : ∀ {k : Ph} → NZ k → k ≢ p0
  nz≢0 nz1 ()
  nz≢0 nz2 ()
  nz≢0 nz3 ()

------------------------------------------------------------------------
-- The phase part is determined by its phases
--
-- The atoms permute nothing, and away from the anchor the phase of the
-- list at an index is its entry there — the anchor's balance never
-- enters.  The list is strictly increasing, so the entry *is* the
-- phase.

-- The phase of a list at an index.
phAt : Fin N → PhList → Ph
phAt t []            = p0
phAt t ((x , k) ∷ l) = phif (δ x t) k +ᵖ phAt t l

-- A phase word permutes nothing.
private
  pw-pow-prm : ∀ (u v : Fin N) (k : ℕ) (t : Fin N) → prm (sp (pw u v ^ k)) t ≡ t
  pw-pow-prm u v zero          t = Eq.refl
  pw-pow-prm u v (suc zero)    t = Eq.refl
  pw-pow-prm u v (suc (suc k)) t = pw-pow-prm u v (suc k) t

atoms-prm : ∀ (l : PhList) (t : Fin N) → prm (sp (atoms l)) t ≡ t
atoms-prm []            t = Eq.refl
atoms-prm ((x , k) ∷ l) t =
  Eq.trans (Eq.cong (prm (sp (atoms l))) (pw-pow-prm x z0 (pn k) t))
           (atoms-prm l t)

-- And its phase at an index off the anchor is the list's.
private
  one-ph : ∀ (x t : Fin N) → t ≢ z0 → ph (sp (pw x z0)) t ≡ phif (δ x t) p1
  one-ph x t ne =
    Eq.trans (Eq.cong (λ z → phif (δ x t) p1 +ᵖ phif z p3) (δ-≢ z0 t ne))
             (+ᵖ-idʳ (phif (δ x t) p1))

  sum2 : ∀ (b : Bool) → phif b p1 +ᵖ phif b p1 ≡ phif b p2
  sum2 true  = Eq.refl
  sum2 false = Eq.refl

aw-ph : ∀ (x : Fin N) (k : Ph) (t : Fin N) → t ≢ z0 →
        ph (sp (aw x k)) t ≡ phif (δ x t) k
aw-ph x p0 t ne = phif0 (δ x t)
  where
  phif0 : ∀ b → p0 ≡ phif b p0
  phif0 true  = Eq.refl
  phif0 false = Eq.refl
aw-ph x p1 t ne = one-ph x t ne
aw-ph x p2 t ne =
  Eq.trans (Eq.cong₂ _+ᵖ_ (one-ph x t ne) (one-ph x t ne)) (go (δ x t))
  where
  go : ∀ b → phif b p1 +ᵖ phif b p1 ≡ phif b p2
  go true  = Eq.refl
  go false = Eq.refl
aw-ph x p3 t ne =
  Eq.trans (Eq.cong₂ _+ᵖ_ (one-ph x t ne)
                          (Eq.cong₂ _+ᵖ_ (one-ph x t ne) (one-ph x t ne)))
           (go (δ x t))
  where
  go : ∀ b → phif b p1 +ᵖ (phif b p1 +ᵖ phif b p1) ≡ phif b p3
  go true  = Eq.refl
  go false = Eq.refl

atoms-ph : ∀ (l : PhList) (t : Fin N) → t ≢ z0 →
           ph (sp (atoms l)) t ≡ phAt t l
atoms-ph []            t ne = Eq.refl
atoms-ph ((x , k) ∷ l) t ne =
  Eq.cong₂ _+ᵖ_ (aw-ph x k t ne)
    (Eq.trans (Eq.cong (ph (sp (atoms l))) (pw-pow-prm x z0 (pn k) t))
              (atoms-ph l t ne))

------------------------------------------------------------------------
-- The phase of an increasing list

-- Nothing at or below the bound occurs.
phAt-below : ∀ {lo : ℕ} (t : Fin N) (l : PhList) →
             Incr lo l → toℕ t ≤ lo → phAt t l ≡ p0
phAt-below t []            nil         le = Eq.refl
phAt-below t ((x , k) ∷ l) (cons lt i) le =
  Eq.trans (Eq.cong₂ _+ᵖ_
             (Eq.cong (λ b → phif b k)
               (δ-≢ x t (λ e → n≮n (toℕ x)
                                   (Eq.subst (_< toℕ x) (Eq.cong toℕ e)
                                             (≤-<-trans le lt)))))
             (phAt-below t l i (≤-trans le (<⇒≤ lt))))
           Eq.refl

-- The head's entry is read off at the head.
phAt-head : ∀ (x : Fin N) (k : Ph) (l : PhList) → Incr (toℕ x) l →
            phAt x ((x , k) ∷ l) ≡ k
phAt-head x k l i =
  Eq.trans (Eq.cong₂ _+ᵖ_ (Eq.cong (λ b → phif b k) (δ-here x))
                          (phAt-below x l i ≤-refl))
           (+ᵖ-idʳ k)

-- Anything strictly below the head reads zero.
phAt-out : ∀ (x y : Fin N) (k : Ph) (l : PhList) → toℕ x < toℕ y →
           Incr (toℕ y) l → phAt x ((y , k) ∷ l) ≡ p0
phAt-out x y k l lt i =
  Eq.trans (Eq.cong₂ _+ᵖ_
             (Eq.cong (λ b → phif b k)
               (δ-≢ y x (λ e → n≮n (toℕ y)
                                   (Eq.subst (_< toℕ y) (Eq.cong toℕ e) lt))))
             (phAt-below x l i (<⇒≤ lt)))
           Eq.refl

-- Two increasing non-zero lists with the same phases are the same list.
incr-unique : ∀ (l l′ : PhList) → Incr 0 l → Incr 0 l′ → NZL l → NZL l′ →
              (∀ t → phAt t l ≡ phAt t l′) → l ≡ l′
incr-unique []            []              i i′ z z′ e = Eq.refl
incr-unique []            ((y , k) ∷ l′)  i (cons _ i′) z (cons zk z′) e =
  ⊥-elim (nz≢0 zk (Eq.trans (Eq.sym (phAt-head y k l′ i′)) (Eq.sym (e y))))
incr-unique ((x , k) ∷ l) []              (cons _ i) i′ (cons zk z) z′ e =
  ⊥-elim (nz≢0 zk (Eq.trans (Eq.sym (phAt-head x k l i)) (e x)))
incr-unique ((x , k) ∷ l) ((y , k′) ∷ l′) (cons _ i) (cons _ i′)
            (cons zk z) (cons zk′ z′) e = heads (<-cmp (toℕ x) (toℕ y))
  where
  tail : x ≡ y → k ≡ k′ → l ≡ l′
  tail Eq.refl Eq.refl =
    incr-unique l l′ (Incr-mono z≤n i) (Incr-mono z≤n i′) z z′ cancel
    where
    cancel : ∀ t → phAt t l ≡ phAt t l′
    cancel t = +ᵖ-cancelʳ-left (phif (δ x t) k) _ _ (e t)
      where
      +ᵖ-cancelʳ-left : ∀ (c u v : Ph) → c +ᵖ u ≡ c +ᵖ v → u ≡ v
      +ᵖ-cancelʳ-left c u v eq =
        +ᵖ-cancelʳ c u v (Eq.trans (+ᵖ-comm u c) (Eq.trans eq (+ᵖ-comm c v)))

  phases : x ≡ y → k ≡ k′
  phases Eq.refl =
    Eq.trans (Eq.sym (phAt-head x k l i))
             (Eq.trans (e x) (phAt-head x k′ l′ i′))

  heads : Tri (toℕ x < toℕ y) (toℕ x ≡ toℕ y) (toℕ y < toℕ x) →
          (x , k) ∷ l ≡ (y , k′) ∷ l′
  heads (tri< lt _ _) =
    ⊥-elim (nz≢0 zk (Eq.trans (Eq.sym (phAt-head x k l i))
                              (Eq.trans (e x) (phAt-out x y k′ l′ lt i′))))
  heads (tri≈ _ eq _) =
    Eq.cong₂ _∷_
      (Eq.cong₂ _,_ (toℕ-injective eq) (phases (toℕ-injective eq)))
      (tail (toℕ-injective eq) (phases (toℕ-injective eq)))
  heads (tri> _ _ gt) =
    ⊥-elim (nz≢0 zk′ (Eq.trans (Eq.sym (phAt-head y k′ l′ i′))
                               (Eq.trans (Eq.sym (e y)) (phAt-out y x k l gt i))))

------------------------------------------------------------------------
-- The permutation of a word is injective

private
  n≢sn : ∀ (j : ℕ) → j ≢ suc j
  n≢sn (suc j) e = n≢sn j (suc-injective e)

gen-prm-inj : ∀ (g : GenP N) {i j : Fin N} →
              prm (spg g) i ≡ prm (spg g) j → i ≡ j
gen-prm-inj (pp a b)         e = e
gen-prm-inj (px c a b _)     e = swapF-inj a b e
gen-prm-inj (dx a b c d _ _) e = swapF-inj a b (swapF-inj c d e)
gen-prm-inj (ki a b s _) e = e

prm-inj : ∀ (w : W) {i j : Fin N} → prm (sp w) i ≡ prm (sp w) j → i ≡ j
prm-inj [ g ]ʷ  e = gen-prm-inj g e
prm-inj ε       e = e
prm-inj (u • v) e = prm-inj u (prm-inj v e)

------------------------------------------------------------------------
-- How a letter on a consecutive pair acts

Bnd : ℕ → ℕ → Set
Bnd v L = ∀ e → e < L → suc (v + e) < N

private
  bnd-hd : ∀ {v L} → Bnd v (suc L) → suc v < N
  bnd-hd {v} b = Eq.subst (λ z → suc z < N) (+-identityʳ v) (b 0 (s≤s z≤n))

  bnd-tl : ∀ {v L} → Bnd v (suc L) → Bnd (suc v) L
  bnd-tl {v} b e lt = Eq.subst (λ z → suc z < N) (+-suc v e) (b (suc e) (s≤s lt))

sx-prm : ∀ (j : ℕ) (q : j < N) (p : suc j < N) (t : Fin N) →
         prm (sp (sx j)) t ≡ swapF (fin j q) (fin (suc j) p) t
sx-prm j q p t =
  Eq.trans (Eq.cong (λ w → prm (sp w) t) (sx-letter j p))
           (Eq.cong₂ (λ a b → swapF a b t) (fin-irr j (j<sj<N p) q) Eq.refl)

-- It moves its own index up by one.
sx-at : ∀ (j : ℕ) (q : j < N) (p : suc j < N) (t : Fin N) → toℕ t ≡ j →
        toℕ (prm (sp (sx j)) t) ≡ suc j
sx-at j q p t e =
  Eq.trans (Eq.cong toℕ
             (Eq.trans (sx-prm j q p t)
                       (Eq.trans (Eq.cong (swapF (fin j q) (fin (suc j) p)) t≡)
                                 (swapF-a (fin j q) (fin (suc j) p)))))
           (fin-toℕ (suc j) p)
  where
  t≡ : t ≡ fin j q
  t≡ = toℕ-injective (Eq.trans e (Eq.sym (fin-toℕ j q)))

-- And leaves every other index alone.
sx-off : ∀ (j : ℕ) (q : j < N) (p : suc j < N) (t : Fin N) →
         toℕ t ≢ j → toℕ t ≢ suc j → prm (sp (sx j)) t ≡ t
sx-off j q p t nj nsj =
  Eq.trans (sx-prm j q p t)
           (swapF-o (fin j q) (fin (suc j) p) t
                    (λ e → nj (Eq.trans (Eq.cong toℕ e) (fin-toℕ j q)))
                    (λ e → nsj (Eq.trans (Eq.cong toℕ e) (fin-toℕ (suc j) p))))

-- Squaring it is the identity.
sx-invol : ∀ (j : ℕ) (q : j < N) (p : suc j < N) (t : Fin N) →
           prm (sp (sx j)) (prm (sp (sx j)) t) ≡ t
sx-invol j q p t =
  Eq.trans (Eq.cong (prm (sp (sx j))) (sx-prm j q p t))
           (Eq.trans (sx-prm j q p _) (swapF-invol (fin j q) (fin (suc j) p) t))

------------------------------------------------------------------------
-- How a run acts

run-lo : ∀ (v L : ℕ) → Bnd v L → ∀ (t : Fin N) → toℕ t < v →
         prm (sp (runFrom v L)) t ≡ t
run-lo v zero    b t lt = Eq.refl
run-lo v (suc L) b t lt =
  Eq.trans (Eq.cong (prm (sp (runFrom (suc v) L)))
                    (sx-off v (<-trans (n<1+n v) (bnd-hd b)) (bnd-hd b) t
                            (λ e → n≮n v (Eq.subst (_< v) e lt))
                            (λ e → n≮n v (<-trans (n<1+n v) (Eq.subst (_< v) e lt)))))
           (run-lo (suc v) L (bnd-tl b) t (<-trans lt (n<1+n v)))

run-hi : ∀ (v L : ℕ) → Bnd v L → ∀ (t : Fin N) → v + L < toℕ t →
         prm (sp (runFrom v L)) t ≡ t
run-hi v zero    b t lt = Eq.refl
run-hi v (suc L) b t lt =
  Eq.trans (Eq.cong (prm (sp (runFrom (suc v) L)))
                    (sx-off v (<-trans (n<1+n v) (bnd-hd b)) (bnd-hd b) t
                            (λ e → n≮n (toℕ t) (Eq.subst (_< toℕ t) (Eq.sym e) v<t))
                            (λ e → n≮n (toℕ t) (Eq.subst (_< toℕ t) (Eq.sym e) sv<t))))
           (run-hi (suc v) L (bnd-tl b) t lt′)
  where
  lt′ : suc v + L < toℕ t
  lt′ = Eq.subst (_< toℕ t) (+-suc v L) lt

  sv<t : suc v < toℕ t
  sv<t = ≤-<-trans (s≤s (m≤m+n v L)) lt′

  v<t : v < toℕ t
  v<t = <-trans (n<1+n v) sv<t

run-send : ∀ (v L : ℕ) → Bnd v L → ∀ (t : Fin N) → toℕ t ≡ v →
           toℕ (prm (sp (runFrom v L)) t) ≡ v + L
run-send v zero    b t e = Eq.trans e (Eq.sym (+-identityʳ v))
run-send v (suc L) b t e =
  Eq.trans (run-send (suc v) L (bnd-tl b) _
                     (sx-at v (<-trans (n<1+n v) (bnd-hd b)) (bnd-hd b) t e))
           (Eq.sym (+-suc v L))

------------------------------------------------------------------------
-- A run is a bijection

runBack : ℕ → ℕ → W
runBack v zero    = ε
runBack v (suc L) = runBack (suc v) L • sx v

run-back : ∀ (v L : ℕ) → Bnd v L → ∀ (t : Fin N) →
           prm (sp (runBack v L)) (prm (sp (runFrom v L)) t) ≡ t
run-back v zero    b t = Eq.refl
run-back v (suc L) b t =
  Eq.trans (Eq.cong (prm (sp (sx v)))
                    (run-back (suc v) L (bnd-tl b) (prm (sp (sx v)) t)))
           (sx-invol v (<-trans (n<1+n v) (bnd-hd b)) (bnd-hd b) t)

run-forth : ∀ (v L : ℕ) → Bnd v L → ∀ (t : Fin N) →
            prm (sp (runFrom v L)) (prm (sp (runBack v L)) t) ≡ t
run-forth v zero    b t = Eq.refl
run-forth v (suc L) b t =
  Eq.trans (Eq.cong (prm (sp (runFrom (suc v) L)))
                    (sx-invol v (<-trans (n<1+n v) (bnd-hd b)) (bnd-hd b)
                              (prm (sp (runBack (suc v) L)) t)))
           (run-forth (suc v) L (bnd-tl b) t)

------------------------------------------------------------------------
-- The i-th run, in its place

private
  runBnd : ∀ (i k v : ℕ) → 1 ≤ i → N ∸ i ≡ k → v ≤ k → Bnd v (k ∸ v)
  runBnd = run-bounds

  pred< : ∀ (P : ℕ) → 0 < P → P ∸ 1 < P
  pred< (suc P) _ = s≤s ≤-refl

runAt-hi : ∀ (i k v : ℕ) → 1 ≤ i → N ∸ i ≡ k → v ≤ k →
           ∀ (t : Fin N) → k < toℕ t → prm (sp (runAt i v)) t ≡ t
runAt-hi i k v 1i Ni vk t lt =
  Eq.trans (Eq.cong (λ w → prm (sp w) t) (runAt≡ i v Ni))
           (run-hi v (k ∸ v) (runBnd i k v 1i Ni vk) t
                   (Eq.subst (_< toℕ t) (Eq.sym (m+[n∸m]≡n vk)) lt))

runAt-send : ∀ (i k v : ℕ) → 1 ≤ i → N ∸ i ≡ k → v ≤ k →
             ∀ (t : Fin N) → toℕ t ≡ v → toℕ (prm (sp (runAt i v)) t) ≡ k
runAt-send i k v 1i Ni vk t e =
  Eq.trans (Eq.cong (λ w → toℕ (prm (sp w) t)) (runAt≡ i v Ni))
           (Eq.trans (run-send v (k ∸ v) (runBnd i k v 1i Ni vk) t e)
                     (m+[n∸m]≡n vk))

permFrom-hi : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ k → Lehmer d →
              ∀ (t : Fin N) → k < toℕ t → prm (sp (permFrom i k d)) t ≡ t
permFrom-hi i zero    d 1i Ni L t lt = Eq.refl
permFrom-hi i (suc k) d 1i Ni L t lt =
  Eq.trans (Eq.cong (prm (sp (permFrom (suc i) k d)))
                    (runAt-hi i (suc k) (d i) 1i Ni vk t lt))
           (permFrom-hi (suc i) k d (s≤s z≤n) (shift-Ni i k Ni) L t
                        (<-trans (n<1+n k) lt))
  where
  vk : d i ≤ suc k
  vk = Eq.subst (d i ≤_) Ni (L i)

code-at : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ suc k → Lehmer d →
          ∀ (t : Fin N) → toℕ t ≡ d i →
          toℕ (prm (sp (permFrom i (suc k) d)) t) ≡ suc k
code-at i k d 1i Ni L t e =
  Eq.trans (Eq.cong toℕ
             (permFrom-hi (suc i) k d (s≤s z≤n) (shift-Ni i k Ni) L
                          (prm (sp (runAt i (d i))) t) mid))
           (runAt-send i (suc k) (d i) 1i Ni vk t e)
  where
  vk : d i ≤ suc k
  vk = Eq.subst (d i ≤_) Ni (L i)

  mid : k < toℕ (prm (sp (runAt i (d i))) t)
  mid = Eq.subst (k <_) (Eq.sym (runAt-send i (suc k) (d i) 1i Ni vk t e)) (n<1+n k)

------------------------------------------------------------------------
-- The permutation part is determined by its permutation

perm-unique : ∀ (i k : ℕ) (d d′ : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ k →
              Lehmer d → Lehmer d′ →
              (∀ t → prm (sp (permFrom i k d)) t ≡ prm (sp (permFrom i k d′)) t) →
              permFrom i k d ≡ permFrom i k d′
perm-unique i zero    d d′ 1i Ni L L′ e = Eq.refl
perm-unique i (suc k) d d′ 1i Ni L L′ e =
  Eq.cong₂ _•_ (Eq.cong (runAt i) same) tails
  where
  vk  : d i ≤ suc k
  vk  = Eq.subst (d i ≤_) Ni (L i)
  vk′ : d′ i ≤ suc k
  vk′ = Eq.subst (d′ i ≤_) Ni (L′ i)

  0<N : 0 < N
  0<N = s≤s z≤n

  bound : ∀ (v : ℕ) → v ≤ N ∸ i → v < N
  bound v le = ≤-<-trans (≤-trans le (∸-monoʳ-≤ N 1i)) (pred< N 0<N)

  q  = bound (d i)  (L i)
  q′ = bound (d′ i) (L′ i)

  t  = fin (d i)  q
  t′ = fin (d′ i) q′

  same : d i ≡ d′ i
  same =
    Eq.trans (Eq.sym (fin-toℕ (d i) q))
             (Eq.trans (Eq.cong toℕ (prm-inj (permFrom i (suc k) d) pins))
                       (fin-toℕ (d′ i) q′))
    where
    at  : toℕ (prm (sp (permFrom i (suc k) d)) t) ≡ suc k
    at  = code-at i k d 1i Ni L t (fin-toℕ (d i) q)

    at′ : toℕ (prm (sp (permFrom i (suc k) d′)) t′) ≡ suc k
    at′ = code-at i k d′ 1i Ni L′ t′ (fin-toℕ (d′ i) q′)

    pins : prm (sp (permFrom i (suc k) d)) t ≡ prm (sp (permFrom i (suc k) d)) t′
    pins = toℕ-injective
             (Eq.trans at (Eq.sym (Eq.trans (Eq.cong toℕ (e t′)) at′)))

  tails : permFrom (suc i) k d ≡ permFrom (suc i) k d′
  tails = perm-unique (suc i) k d d′ (s≤s z≤n) (shift-Ni i k Ni) L L′ cancel
    where
    cancel : ∀ s → prm (sp (permFrom (suc i) k d)) s
                 ≡ prm (sp (permFrom (suc i) k d′)) s
    cancel s =
      Eq.trans (Eq.sym (Eq.cong (prm (sp (permFrom (suc i) k d))) step))
               (Eq.trans (e u) (Eq.cong (prm (sp (permFrom (suc i) k d′))) step′))
      where
      u : Fin N
      u = prm (sp (runBack (d i) (suc k ∸ d i))) s

      step : prm (sp (runAt i (d i))) u ≡ s
      step = Eq.trans (Eq.cong (λ w → prm (sp w) u) (runAt≡ i (d i) Ni))
                      (run-forth (d i) (suc k ∸ d i)
                                 (runBnd i (suc k) (d i) 1i Ni vk) s)

      step′ : prm (sp (runAt i (d′ i))) u ≡ s
      step′ = Eq.trans (Eq.cong (λ v → prm (sp (runAt i v)) u) (Eq.sym same)) step

------------------------------------------------------------------------
-- Uniqueness

unique : ∀ {l l′ : PhList} {d d′ : ℕ → ℕ} →
         Normal l d → Normal l′ d′ → sp (NF l d) ≐ sp (NF l′ d′) →
         NF l d ≡ NF l′ d′
unique {l} {l′} {d} {d′} nm nm′ e = Eq.cong₂ _•_ (Eq.cong atoms lists) perms
  where
  perms : permPart d ≡ permPart d′
  perms = perm-unique 1 (N ∸ 1) d d′ ≤-refl Eq.refl
                      (Normal.lehmer nm) (Normal.lehmer nm′) pe
    where
    pe : ∀ t → prm (sp (permPart d)) t ≡ prm (sp (permPart d′)) t
    pe t =
      Eq.trans (Eq.sym (Eq.cong (prm (sp (permPart d))) (atoms-prm l t)))
               (Eq.trans (prm≡ e t)
                         (Eq.cong (prm (sp (permPart d′))) (atoms-prm l′ t)))

  lists : l ≡ l′
  lists = incr-unique l l′ (Normal.incr nm) (Normal.incr nm′)
                      (Normal.nz nm) (Normal.nz nm′) pheq
    where
    pheq : ∀ t → phAt t l ≡ phAt t l′
    pheq t = go (t ≟ z0)
      where
      go : Dec (t ≡ z0) → phAt t l ≡ phAt t l′
      go (yes Eq.refl) =
        Eq.trans (phAt-below t l (Normal.incr nm) ≤-refl)
                 (Eq.sym (phAt-below t l′ (Normal.incr nm′) ≤-refl))
      go (no ne) =
        +ᵖ-cancelʳ (ph (sp (permPart d)) t) (phAt t l) (phAt t l′) step
        where
        left : ph (sp (NF l d)) t ≡ phAt t l +ᵖ ph (sp (permPart d)) t
        left = Eq.cong₂ _+ᵖ_ (atoms-ph l t ne)
                             (Eq.cong (ph (sp (permPart d))) (atoms-prm l t))

        right : ph (sp (NF l′ d′)) t ≡ phAt t l′ +ᵖ ph (sp (permPart d)) t
        right = Eq.cong₂ _+ᵖ_ (atoms-ph l′ t ne)
                  (Eq.trans (Eq.cong (ph (sp (permPart d′))) (atoms-prm l′ t))
                            (Eq.cong (λ w → ph (sp w) t) (Eq.sym perms)))

        step : phAt t l +ᵖ ph (sp (permPart d)) t
             ≡ phAt t l′ +ᵖ ph (sp (permPart d)) t
        step = Eq.trans (Eq.sym left) (Eq.trans (ph≡ e t) right)

------------------------------------------------------------------------
-- The analogue of Corollary A.5, unconditionally
--
-- Two K-free words with the same phased permutation are equivalent.

A5 : ∀ {u v : W} → KFreeʷ u → KFreeʷ v → sp u ≐ sp v →
     PB._≈_ (N F,_===_) u v
A5 = cor-A5 unique
