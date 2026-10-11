------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the normal form of Lemma A.4
--
-- A word of the form (B) is determined by the signed permutation it
-- denotes, which is the half of Lemma A.4 that `NF` leaves open as
-- `NF.Unique`, and with it Corollary A.5 is unconditional.
--
-- The two parts are read back separately.  The sign part does not
-- permute anything, so the permutation of a normal form is the
-- permutation of its Lehmer code alone; and the code is read off that
-- permutation by the classical inverse — the i-th entry is the index
-- the permutation sends to N − i, because the i-th run sends its first
-- index there and every later run leaves N − i alone.  With the codes
-- equal the permutation parts are the same word, and then the signs
-- agree index by index, which for an increasing list is membership.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Unique (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_ ; toℕ-injective ; toℕ<n)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (zero ; suc ; _+_ ; _<_ ; _≤_ ; _∸_ ; _<?_ ; z≤n ; s≤s)
  renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; <-trans ; ≤-<-trans ; <-≤-trans ; <⇒≤ ; <-cmp ; n≮n
       ; n<1+n ; n≤1+n ; ≮⇒≥ ; ≤∧≢⇒<
       ; suc-injective ; +-identityʳ ; +-suc ; m≤m+n ; m+[n∸m]≡n ; ∸-monoʳ-≤
       ; m∸n≤m ; n∸n≡0 ; 0∸n≡0 ; n≤0⇒n≡0)
  renaming (_≟_ to _≟ⁿ_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
  using (_PF,_===_ ; free⇒full-≈)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
  using (GenP ; −1−1 ; −1X ; XX ; HH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (signOf ; Incr ; Incr₀ ; Even ; Odd ; Incr⇒Incr₀ ; nil ; cons
       ; NF ; Normal ; normal ; Lehmer ; runFrom ; runAt ; permFrom ; permPart
       ; HFreeʷ ; cor-A5
       ; sx ; sx-zx ; fin ; fin-toℕ ; runAt≡ ; run-bounds ; shift-Ni ; idx-bound)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; spg ; sgn ; prm ; _≐_ ; prm≡ ; sgn≡ ; δ ; δ-here ; δ-≢
       ; xor-assoc ; xor-idʳ
       ; sp-zx ; swapF ; swapF-a ; swapF-o ; swapF-invol ; swapF-inj)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- The sign part is determined by its signs
--
-- A sign part permutes nothing, and its sign at an index counts, mod
-- two, how often that index occurs in the list.  The list is strictly
-- increasing, so no index occurs twice and the count *is* membership.

-- Whether an index occurs, counted mod two — which is what the signs
-- of a product of sign pairs give directly.
mem : Fin N → List (Fin N) → Bool
mem t []      = false
mem t (x ∷ l) = δ x t xor mem t l

-- A sign part is a permutation-free word.
signOf-prm : ∀ (l : List (Fin N)) (t : Fin N) → prm (sp (signOf l)) t ≡ t
signOf-prm []          t = Eq.refl
signOf-prm (a ∷ [])    t = Eq.refl
signOf-prm (a ∷ b ∷ l) t = signOf-prm l t

-- And its sign at an index is whether that index occurs.
signOf-sgn : ∀ (l : List (Fin N)) → Even l → ∀ (t : Fin N) →
             sgn (sp (signOf l)) t ≡ mem t l
signOf-sgn []           nil             t = Eq.refl
signOf-sgn (a ∷ [])     (cons ())       t
signOf-sgn (a ∷ b ∷ l) (cons (cons e)) t =
  Eq.trans (Eq.cong (λ z → (δ a t xor δ b t) xor z) (signOf-sgn l e t))
           (xor-assoc (δ a t) (δ b t) (mem t l))

------------------------------------------------------------------------
-- Membership of an increasing list

-- Nothing at or below the bound occurs.
mem-below : ∀ {lo : ℕ} (t : Fin N) (l : List (Fin N)) →
            Incr lo l → toℕ t ≤ lo → mem t l ≡ false
mem-below t []      nil        le = Eq.refl
mem-below t (x ∷ l) (cons lt i) le =
  Eq.trans (Eq.cong (_xor mem t l)
                    (δ-≢ x t (λ e → n≮n (toℕ x)
                                        (Eq.subst (_< toℕ x) (Eq.cong toℕ e)
                                                  (≤-<-trans le lt)))))
           (mem-below t l i (≤-trans le (<⇒≤ lt)))

-- The head occurs.
mem-head : ∀ (x : Fin N) (l : List (Fin N)) → Incr (toℕ x) l → mem x (x ∷ l) ≡ true
mem-head x l i =
  Eq.trans (Eq.cong (_xor mem x l) (δ-here x))
           (Eq.cong (true xor_) (mem-below x l i ≤-refl))

-- Anything strictly below the head does not.
mem-out : ∀ (x y : Fin N) (l : List (Fin N)) → toℕ x < toℕ y → Incr (toℕ y) l →
          mem x (y ∷ l) ≡ false
mem-out x y l lt i =
  Eq.trans (Eq.cong (_xor mem x l)
                    (δ-≢ y x (λ e → n≮n (toℕ y)
                                        (Eq.subst (_< toℕ y) (Eq.cong toℕ e) lt))))
           (mem-below x l i (<⇒≤ lt))

-- So two increasing lists with the same indices are the same list.
incr-unique : ∀ (l l′ : List (Fin N)) → Incr₀ l → Incr₀ l′ →
              (∀ t → mem t l ≡ mem t l′) → l ≡ l′
incr-unique []       []         i  i′        e = Eq.refl
incr-unique []       (y ∷ l′)   i  (cons i′) e =
  ⊥-elim (true≢false (Eq.trans (Eq.sym (mem-head y l′ i′)) (Eq.sym (e y))))
  where
  true≢false : true ≢ false
  true≢false ()
incr-unique (x ∷ l)  []         (cons i) i′  e =
  ⊥-elim (true≢false (Eq.trans (Eq.sym (mem-head x l i)) (e x)))
  where
  true≢false : true ≢ false
  true≢false ()
incr-unique (x ∷ l) (y ∷ l′) (cons i) (cons i′) e = heads (<-cmp (toℕ x) (toℕ y))
  where
  true≢false : true ≢ false
  true≢false ()

  tail : x ≡ y → l ≡ l′
  tail Eq.refl = incr-unique l l′ (Incr⇒Incr₀ i) (Incr⇒Incr₀ i′) cancel
    where
    cancel : ∀ t → mem t l ≡ mem t l′
    cancel t with δ x t | e t
    ... | false | p = p
    ... | true  | p = flip p
      where
      flip : ∀ {u v : Bool} → true xor u ≡ true xor v → u ≡ v
      flip {false} {false} _ = Eq.refl
      flip {true}  {true}  _ = Eq.refl
      flip {false} {true}  ()
      flip {true}  {false} ()

  heads : Tri (toℕ x < toℕ y) (toℕ x ≡ toℕ y) (toℕ y < toℕ x) →
          x ∷ l ≡ y ∷ l′
  heads (tri< lt _ _) =
    ⊥-elim (true≢false (Eq.trans (Eq.sym (mem-head x l i))
                                 (Eq.trans (e x) (mem-out x y l′ lt i′))))
  heads (tri≈ _ eq _) = Eq.cong₂ _∷_ (toℕ-injective eq) (tail (toℕ-injective eq))
  heads (tri> _ _ gt) =
    ⊥-elim (true≢false (Eq.trans (Eq.sym (mem-head y l′ i′))
                                 (Eq.trans (Eq.sym (e y)) (mem-out y x l gt i))))

------------------------------------------------------------------------
-- The permutation of a word is injective

private
  n≢sn : ∀ (j : ℕ) → j ≢ suc j
  n≢sn (suc j) e = n≢sn j (suc-injective e)

  fin≢′ : ∀ (j : ℕ) (q : j < N) (p : suc j < N) → fin j q ≢ fin (suc j) p
  fin≢′ j q p e =
    n≢sn j (Eq.trans (Eq.sym (fin-toℕ j q))
                     (Eq.trans (Eq.cong toℕ e) (fin-toℕ (suc j) p)))

gen-prm-inj : ∀ (g : GenP (₃₊ m)) {i j : Fin N} →
              prm (spg g) i ≡ prm (spg g) j → i ≡ j
gen-prm-inj (−1−1 a b)       e = e
gen-prm-inj (−1X c a b _)    e = swapF-inj a b e
gen-prm-inj (XX a b c d _ _) e = swapF-inj a b (swapF-inj c d e)
gen-prm-inj (HH a b c d _ _) e = e

prm-inj : ∀ (w : W) {i j : Fin N} → prm (sp w) i ≡ prm (sp w) j → i ≡ j
prm-inj [ g ]ʷ  e = gen-prm-inj g e
prm-inj ε       e = e
prm-inj (u • v) e = prm-inj u (prm-inj v e)

------------------------------------------------------------------------
-- How a letter on a consecutive pair acts
--
-- The letters of the permutation part carry natural-number indices, so
-- each fact is stated on `toℕ` and the `Fin` is only built where the
-- letter itself is.

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
  Eq.trans (Eq.cong (λ w → prm (sp w) t) (sx-zx j q p))
           (prm≡ (sp-zx (fin j q) (fin j q) (fin (suc j) p) (fin≢′ j q p)) t)

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
--
-- A run from v of length L moves v to v + L, moves everything strictly
-- between down by one, and fixes everything outside.  Only the first
-- and the last of those are needed.

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
--
-- Its inverse is the same letters in the other order, since each is an
-- involution.  That is what lets the first run be cancelled from an
-- equality of permutations, which is how the induction proceeds.

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
--
-- The runs of (B) have decreasing tops, so the i-th sends its first
-- index to N − i and no later run touches that index again.  The
-- entry of the code is therefore the index the permutation sends to
-- N − i, which is what makes the code readable off the permutation.

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
  0<N = ≤-trans (s≤s z≤n) (Eq.subst (_≤ N) Ni (m∸n≤m N i))

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
                      (run-forth (d i) (suc k ∸ d i) (runBnd i (suc k) (d i) 1i Ni vk) s)

      step′ : prm (sp (runAt i (d′ i))) u ≡ s
      step′ = Eq.trans (Eq.cong (λ v → prm (sp (runAt i v)) u) (Eq.sym same)) step

------------------------------------------------------------------------
-- Lemma A.4, uniqueness

private
  xor-cancelʳ : ∀ (x u v : Bool) → u xor x ≡ v xor x → u ≡ v
  xor-cancelʳ false u v e = Eq.trans (Eq.sym (xor-idʳ u)) (Eq.trans e (xor-idʳ v))
  xor-cancelʳ true false false _ = Eq.refl
  xor-cancelʳ true true  true  _ = Eq.refl

unique : ∀ {l l′ : List (Fin N)} {d d′ : ℕ → ℕ} →
         Normal l d → Normal l′ d′ → sp (NF l d) ≐ sp (NF l′ d′) →
         NF l d ≡ NF l′ d′
unique {l} {l′} {d} {d′} nm nm′ e = Eq.cong₂ _•_ (Eq.cong signOf lists) perms
  where
  perms : permPart d ≡ permPart d′
  perms = perm-unique 1 (N ∸ 1) d d′ ≤-refl Eq.refl
                      (Normal.lehmer nm) (Normal.lehmer nm′) pe
    where
    pe : ∀ t → prm (sp (permPart d)) t ≡ prm (sp (permPart d′)) t
    pe t =
      Eq.trans (Eq.sym (Eq.cong (prm (sp (permPart d))) (signOf-prm l t)))
               (Eq.trans (prm≡ e t)
                         (Eq.cong (prm (sp (permPart d′))) (signOf-prm l′ t)))

  lists : l ≡ l′
  lists = incr-unique l l′ (Normal.incr nm) (Normal.incr nm′) memeq
    where
    memeq : ∀ t → mem t l ≡ mem t l′
    memeq t = xor-cancelʳ (sgn (sp (permPart d)) t) (mem t l) (mem t l′) step
      where
      left : sgn (sp (NF l d)) t ≡ mem t l xor sgn (sp (permPart d)) t
      left = Eq.cong₂ _xor_ (signOf-sgn l (Normal.even nm) t)
                            (Eq.cong (sgn (sp (permPart d))) (signOf-prm l t))

      right : sgn (sp (NF l′ d′)) t ≡ mem t l′ xor sgn (sp (permPart d)) t
      right = Eq.cong₂ _xor_ (signOf-sgn l′ (Normal.even nm′) t)
                             (Eq.trans (Eq.cong (sgn (sp (permPart d′)))
                                                (signOf-prm l′ t))
                                       (Eq.cong (λ w → sgn (sp w) t) (Eq.sym perms)))

      step : mem t l xor sgn (sp (permPart d)) t
           ≡ mem t l′ xor sgn (sp (permPart d)) t
      step = Eq.trans (Eq.sym left) (Eq.trans (sgn≡ e t) right)

------------------------------------------------------------------------
-- Where the letters of a normal form can be
--
-- A word whose permutation fixes every index below some bound has a
-- normal form all of whose letters are at or above it.  That is what
-- says the Hadamard-free part of a word commuting with a Hadamard pair
-- can be written over the indices the pair does not touch, which is
-- what lets it be carried across the pair by (38).
--
-- The argument localises, which is not obvious: the i-th run starts at
-- the index the permutation sends to N − i, so if the permutation
-- fixes that index the run is empty; and a run that is empty, or that
-- starts above the bound, fixes everything below it — so the
-- hypothesis passes to the runs after it and the induction goes
-- through.

-- A run starting above an index leaves it alone.
runAt-low : ∀ (i k v : ℕ) → 1 ≤ i → N ∸ i ≡ k → v ≤ k →
            ∀ (t : Fin N) → toℕ t < v → prm (sp (runAt i v)) t ≡ t
runAt-low i k v 1i Ni vk t lt =
  Eq.trans (Eq.cong (λ w → prm (sp w) t) (runAt≡ i v Ni))
           (run-lo v (k ∸ v) (runBnd i k v 1i Ni vk) t lt)

-- An empty run leaves everything alone.
runAt-empty : ∀ (i v : ℕ) → N ∸ i ∸ v ≡ 0 →
              ∀ (t : Fin N) → prm (sp (runAt i v)) t ≡ t
runAt-empty i v e t = Eq.cong (λ w → prm (sp (runFrom v w)) t) e

module _ (B : ℕ) where

  -- If the runs from the i-th on fix everything below the bound, the
  -- i-th run starts above it or is empty.
  low-start : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ suc k → Lehmer d →
              (∀ (t : Fin N) → toℕ t < B → prm (sp (permFrom i (suc k) d)) t ≡ t) →
              d i < B → d i ≡ suc k
  low-start i k d 1i Ni L fix lt =
    Eq.trans (Eq.sym (fin-toℕ (d i) q))
             (Eq.trans (Eq.cong toℕ (Eq.sym (fix t lt′)))
                       (code-at i k d 1i Ni L t (fin-toℕ (d i) q)))
    where
    0<N : 0 < N
    0<N = ≤-trans (s≤s z≤n) (Eq.subst (_≤ N) Ni (m∸n≤m N i))

    q : d i < N
    q = ≤-<-trans (≤-trans (L i) (∸-monoʳ-≤ N 1i)) (pred< N 0<N)

    t : Fin N
    t = fin (d i) q

    lt′ : toℕ t < B
    lt′ = Eq.subst (_< B) (Eq.sym (fin-toℕ (d i) q)) lt

  -- Either way it fixes everything below the bound …
  runAt-fix : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ suc k → Lehmer d →
              (∀ (t : Fin N) → toℕ t < B → prm (sp (permFrom i (suc k) d)) t ≡ t) →
              ∀ (t : Fin N) → toℕ t < B → prm (sp (runAt i (d i))) t ≡ t
  runAt-fix i k d 1i Ni L fix t lt = go (d i <? B)
    where
    go : Dec (d i < B) → prm (sp (runAt i (d i))) t ≡ t
    go (yes p) = runAt-empty i (d i)
                   (Eq.trans (Eq.cong (_∸ d i) Ni)
                     (Eq.trans (Eq.cong (λ z → suc k ∸ z)
                                        (low-start i k d 1i Ni L fix p))
                               (n∸n≡0 (suc k))))
                   t
    go (no ¬p) = runAt-low i (suc k) (d i) 1i Ni (Eq.subst (d i ≤_) Ni (L i)) t
                           (<-≤-trans lt (≮⇒≥ ¬p))

  -- … so the hypothesis passes to the runs after it.
  low-tail : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ suc k → Lehmer d →
             (∀ (t : Fin N) → toℕ t < B → prm (sp (permFrom i (suc k) d)) t ≡ t) →
             ∀ (t : Fin N) → toℕ t < B → prm (sp (permFrom (suc i) k d)) t ≡ t
  low-tail i k d 1i Ni L fix t lt =
    Eq.trans (Eq.sym (Eq.cong (prm (sp (permFrom (suc i) k d)))
                              (runAt-fix i k d 1i Ni L fix t lt)))
             (fix t lt)

  -- And so every run that starts below the bound is empty.
  low-runs : ∀ (k i : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ k → Lehmer d →
             (∀ (t : Fin N) → toℕ t < B → prm (sp (permFrom i k d)) t ≡ t) →
             ∀ (j : ℕ) → i ≤ j → d j < B → N ∸ j ∸ d j ≡ 0
  low-runs zero i d 1i Ni L fix j ij lt =
    Eq.trans (Eq.cong (_∸ d j) top) (0∸n≡0 (d j))
    where
    top : N ∸ j ≡ 0
    top = n≤0⇒n≡0 (Eq.subst (N ∸ j ≤_) Ni (∸-monoʳ-≤ N ij))
  low-runs (suc k) i d 1i Ni L fix j ij lt = go (i ≟ⁿ j)
    where
    go : Dec (i ≡ j) → N ∸ j ∸ d j ≡ 0
    go (yes Eq.refl) =
      Eq.trans (Eq.cong (_∸ d i) Ni)
               (Eq.trans (Eq.cong (λ z → suc k ∸ z) (low-start i k d 1i Ni L fix lt))
                         (n∸n≡0 (suc k)))
    go (no ne) =
      low-runs k (suc i) d (s≤s z≤n) (shift-Ni i k Ni) L
               (low-tail i k d 1i Ni L fix) j (≤∧≢⇒< ij ne) lt

------------------------------------------------------------------------
-- And what sign it carries there
--
-- A letter on a consecutive pair carries the sign of its own index, so
-- a permutation part whose runs all start high carries no sign at a
-- low index.  With the permutation fixed there too, the sign part's
-- list must avoid the low indices — which is what lets the sign part
-- be carried across a Hadamard pair as well.

-- The sign a letter on a consecutive pair carries is its own index's.
sx-sgn : ∀ (j : ℕ) (q : j < N) (p : suc j < N) (t : Fin N) →
         sgn (sp (sx j)) t ≡ δ (fin j q) t
sx-sgn j q p t =
  Eq.trans (Eq.cong (λ w → sgn (sp w) t) (sx-zx j q p))
           (Eq.trans (sgn≡ (sp-zx (fin j q) (fin j q) (fin (suc j) p) (fin≢′ j q p)) t)
                     (xor-idʳ (δ (fin j q) t)))

-- So a run above an index carries no sign there.
run-sgn-lo : ∀ (v L : ℕ) → Bnd v L → ∀ (t : Fin N) → toℕ t < v →
             sgn (sp (runFrom v L)) t ≡ false
run-sgn-lo v zero    b t lt = Eq.refl
run-sgn-lo v (suc L) b t lt =
  Eq.cong₂ _xor_ head (Eq.trans (Eq.cong (sgn (sp (runFrom (suc v) L))) fixed) tail)
  where
  p = bnd-hd b
  q = <-trans (n<1+n v) p

  t≢v : toℕ t ≢ v
  t≢v e = n≮n v (Eq.subst (_< v) e lt)

  t≢sv : toℕ t ≢ suc v
  t≢sv e = n≮n v (<-trans (n<1+n v) (Eq.subst (_< v) e lt))

  head : sgn (sp (sx v)) t ≡ false
  head = Eq.trans (sx-sgn v q p t)
                  (δ-≢ (fin v q) t (λ e → t≢v (Eq.trans (Eq.cong toℕ e) (fin-toℕ v q))))

  fixed : prm (sp (sx v)) t ≡ t
  fixed = sx-off v q p t t≢v t≢sv

  tail : sgn (sp (runFrom (suc v) L)) t ≡ false
  tail = run-sgn-lo (suc v) L (bnd-tl b) t (<-trans lt (n<1+n v))

-- Whichever way the i-th run starts, it neither moves a low index nor
-- signs it, as long as a run starting low is empty.
module _ (i k : ℕ) (d : ℕ → ℕ) (1i : 1 ≤ i) (Ni : N ∸ i ≡ suc k) (L : Lehmer d)
         (low : ∀ (j : ℕ) → i ≤ j → d j < 4 → N ∸ j ∸ d j ≡ 0)
  where

  private
    dk : d i ≤ suc k
    dk = Eq.subst (d i ≤_) Ni (L i)

  runAt-low-fix : ∀ (t : Fin N) → toℕ t < 4 → prm (sp (runAt i (d i))) t ≡ t
  runAt-low-fix t lt = go (d i <? 4)
    where
    go : Dec (d i < 4) → prm (sp (runAt i (d i))) t ≡ t
    go (yes p) = runAt-empty i (d i) (low i ≤-refl p) t
    go (no ¬p) = runAt-low i (suc k) (d i) 1i Ni dk t (<-≤-trans lt (≮⇒≥ ¬p))

  runAt-low-sgn : ∀ (t : Fin N) → toℕ t < 4 → sgn (sp (runAt i (d i))) t ≡ false
  runAt-low-sgn t lt = go (d i <? 4)
    where
    go : Dec (d i < 4) → sgn (sp (runAt i (d i))) t ≡ false
    go (yes p) = Eq.cong (λ w → sgn (sp (runFrom (d i) w)) t) (low i ≤-refl p)
    go (no ¬p) =
      Eq.trans (Eq.cong (λ w → sgn (sp w) t) (runAt≡ i (d i) Ni))
               (run-sgn-lo (d i) (suc k ∸ d i) (runBnd i (suc k) (d i) 1i Ni dk) t
                           (<-≤-trans lt (≮⇒≥ ¬p)))

-- Hence the whole permutation part carries no sign at a low index.
permFrom-sgn : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ k → Lehmer d →
               (∀ (j : ℕ) → i ≤ j → d j < 4 → N ∸ j ∸ d j ≡ 0) →
               ∀ (t : Fin N) → toℕ t < 4 → sgn (sp (permFrom i k d)) t ≡ false
permFrom-sgn i zero    d 1i Ni L low t lt = Eq.refl
permFrom-sgn i (suc k) d 1i Ni L low t lt =
  Eq.cong₂ _xor_ (runAt-low-sgn i k d 1i Ni L low t lt)
                 (Eq.trans (Eq.cong (sgn (sp (permFrom (suc i) k d)))
                                    (runAt-low-fix i k d 1i Ni L low t lt))
                           (permFrom-sgn (suc i) k d (s≤s z≤n) (shift-Ni i k Ni) L
                                         (λ j ij → low j (≤-trans (n≤1+n i) ij)) t lt))

-- And the permutation part leaves a low index where it is.
permFrom-fix : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ k → Lehmer d →
               (∀ (j : ℕ) → i ≤ j → d j < 4 → N ∸ j ∸ d j ≡ 0) →
               ∀ (t : Fin N) → toℕ t < 4 → prm (sp (permFrom i k d)) t ≡ t
permFrom-fix i zero    d 1i Ni L low t lt = Eq.refl
permFrom-fix i (suc k) d 1i Ni L low t lt =
  Eq.trans (Eq.cong (prm (sp (permFrom (suc i) k d)))
                    (runAt-low-fix i k d 1i Ni L low t lt))
           (permFrom-fix (suc i) k d (s≤s z≤n) (shift-Ni i k Ni) L
                         (λ j ij → low j (≤-trans (n≤1+n i) ij)) t lt)

------------------------------------------------------------------------
-- A normal form over the high indices
--
-- Putting the two together: if a normal form neither moves nor signs
-- any index below 4, then every run of its permutation part starts at
-- 4 or above and every index of its sign part is 4 or above.  Those
-- are exactly the two things `Passes` needs.

-- A list all of whose indices are high.
data High : List (Fin N) → Set where
  nil  : High []
  cons : ∀ {x l} → 4 ≤ toℕ x → High l → High (x ∷ l)

private
  true≢false′ : true ≢ false
  true≢false′ ()

-- An increasing list none of whose indices occurs low is high: its
-- head occurs, so the head is high, and the rest is above the head.
incr-high : ∀ (l : List (Fin N)) → Incr₀ l →
            (∀ (t : Fin N) → toℕ t < 4 → mem t l ≡ false) → High l
incr-high []      nil      h = nil
incr-high (x ∷ l) (cons i) h = cons 4x (incr-high l (Incr⇒Incr₀ i) tail-h)
  where
  4x : 4 ≤ toℕ x
  4x = go (toℕ x <? 4)
    where
    go : Dec (toℕ x < 4) → 4 ≤ toℕ x
    go (yes p) = ⊥-elim (true≢false′ (Eq.trans (Eq.sym (mem-head x l i)) (h x p)))
    go (no ¬p) = ≮⇒≥ ¬p

  tail-h : ∀ (t : Fin N) → toℕ t < 4 → mem t l ≡ false
  tail-h t lt =
    Eq.trans (Eq.sym (Eq.cong (_xor mem t l)
                              (δ-≢ x t (λ e → n≮n (toℕ t)
                                (Eq.subst (toℕ t <_) (Eq.cong toℕ (Eq.sym e))
                                          (<-≤-trans lt 4x))))))
             (h t lt)

module NFHigh (l : List (Fin N)) (d : ℕ → ℕ) (nm : Normal l d)
              (fix  : ∀ (t : Fin N) → toℕ t < 4 → prm (sp (NF l d)) t ≡ t)
              (sgn0 : ∀ (t : Fin N) → toℕ t < 4 → sgn (sp (NF l d)) t ≡ false)
  where

  private
    perm-fix : ∀ (t : Fin N) → toℕ t < 4 → prm (sp (permPart d)) t ≡ t
    perm-fix t lt =
      Eq.trans (Eq.sym (Eq.cong (prm (sp (permPart d))) (signOf-prm l t))) (fix t lt)

  -- Every run that would start low is empty.
  nf-low-runs : ∀ (j : ℕ) → 1 ≤ j → d j < 4 → N ∸ j ∸ d j ≡ 0
  nf-low-runs = low-runs 4 (N ∸ 1) 1 d ≤-refl Eq.refl (Normal.lehmer nm) perm-fix

  -- So the permutation part carries no low sign, and the sign part's
  -- list must be the one carrying none either.
  private
    mem-low : ∀ (t : Fin N) → toℕ t < 4 → mem t l ≡ false
    mem-low t lt =
      Eq.trans (Eq.sym (xor-idʳ (mem t l)))
               (Eq.trans (Eq.cong (mem t l xor_) (Eq.sym pd))
                         (Eq.trans (Eq.sym split) (sgn0 t lt)))
      where
      pd : sgn (sp (permPart d)) t ≡ false
      pd = permFrom-sgn 1 (N ∸ 1) d ≤-refl Eq.refl (Normal.lehmer nm) nf-low-runs t lt

      split : sgn (sp (NF l d)) t ≡ mem t l xor sgn (sp (permPart d)) t
      split = Eq.cong₂ _xor_ (signOf-sgn l (Normal.even nm) t)
                             (Eq.cong (sgn (sp (permPart d))) (signOf-prm l t))

  nf-high : High l
  nf-high = incr-high l (Normal.incr nm) mem-low

------------------------------------------------------------------------
-- Corollary A.5, unconditionally
--
-- With Lemma A.4 complete, two Hadamard-free words with the same
-- signed permutation are equivalent — in the fragment, and so in
-- Figure 8.  This is what the rest of Appendix A.4.2 rests on.

A5 : ∀ {u v : W} → HFreeʷ u → HFreeʷ v → sp u ≐ sp v → PB._≈_ (m PF,_===_) u v
A5 = cor-A5 unique

A5-full : ∀ {u v : W} → HFreeʷ u → HFreeʷ v → sp u ≐ sp v → PB._≈_ (m P,_===_) u v
A5-full hu hv e = free⇒full-≈ (A5 hu hv e)
