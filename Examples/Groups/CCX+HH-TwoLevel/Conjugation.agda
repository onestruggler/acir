------------------------------------------------------------------------
-- Presentations of groups
--
-- From basic edges to all edges (the role of Lemma A.19).
--
-- The basic generators are (-1)_[0], X_[x,x+1] and K_[0,1,2,3]
-- (Definition A.17).  Every other generator is X g′ X for an adjacent
-- transposition X and a generator g′ closer to a basic one (relations
-- (3a), (3c) and (3d)–(3g)), with indices no larger.  Along X g′ X the
-- states are permutations of s and of g·s by such X's, so if s and g·s
-- lie at most at L, so do they all (Levels.mono-level-≤).  Hence the
-- edges of all generators at L follow from those of the basic ones at
-- L and from the edges below L (edges≤).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _∸_)

module Examples.Groups.CCX+HH-TwoLevel.Conjugation {n : ℕ} where

open import Data.Fin.Base as Fin using (Fin ; toℕ ; _<_ ; _≤_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (Lvl ; level ; _<ₗ_)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (top)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (Bℓ ; mono-level-≤)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (conj ; conj′)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {n}
  using (Path ; path-• ; EdgesBelow ; back ; act-gg ; sound-act ; _≤ₗ_)
open import Examples.Groups.CCX+HH-TwoLevel.PathTools {n} using (path-cong)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})

------------------------------------------------------------------------
-- Basic generators

Basic : Gen n → Set
Basic (M-gen a)             = toℕ a ≡ 0
Basic (X-gen a b _)         = toℕ b ≡ suc (toℕ a)
Basic (K-gen a b c d _ _ _) = toℕ a ≡ 0 × toℕ b ≡ 1 × toℕ c ≡ 2 × toℕ d ≡ 3

-- The distance to a basic generator.
size : Gen n → ℕ
size (M-gen a)             = toℕ a
size (X-gen a b _)         = toℕ b ∸ toℕ a
size (K-gen a b c d _ _ _) = toℕ a ℕ.+ toℕ b ℕ.+ toℕ c ℕ.+ toℕ d

------------------------------------------------------------------------
-- Neighbouring indices

private
  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

  suc-∸1 : ∀ m → 0 ℕ.< m → suc (m ∸ 1) ≡ m
  suc-∸1 (suc m) _ = ≡.refl

  -- The index before a positive one.
  predF : (a : Fin n) → 0 ℕ.< toℕ a → Fin n
  predF a h = Fin.fromℕ< {toℕ a ∸ 1} (ℕP.≤-<-trans (ℕP.m∸n≤m (toℕ a) 1) (FinP.toℕ<n a))

  toℕ-predF : ∀ a h → suc (toℕ (predF a h)) ≡ toℕ a
  toℕ-predF a h = ≡.trans (≡.cong suc (FinP.toℕ-fromℕ< _)) (suc-∸1 (toℕ a) h)

  predF< : ∀ a h → predF a h < a
  predF< a h = ≡.subst (toℕ (predF a h) ℕ.<_) (toℕ-predF a h) (ℕP.n<1+n _)

  -- The index after one below another.
  sucF : (a b : Fin n) → suc (toℕ a) ℕ.< toℕ b → Fin n
  sucF a b h = Fin.fromℕ< {suc (toℕ a)} (ℕP.<-trans h (FinP.toℕ<n b))

  toℕ-sucF : ∀ a b h → toℕ (sucF a b h) ≡ suc (toℕ a)
  toℕ-sucF a b h = FinP.toℕ-fromℕ< _

  -- Removing one from a positive difference.
  ∸-suc< : ∀ a b → a ℕ.< b → b ∸ suc a ℕ.< b ∸ a
  ∸-suc< zero (suc b) _ = ℕP.n<1+n b
  ∸-suc< (suc a) (suc b) (ℕ.s≤s lt) = ∸-suc< a b lt

  pos : ∀ {m k} → m ≢ k → k ℕ.≤ m → k ℕ.< m
  pos m≢k k≤m = ℕP.≤∧≢⇒< k≤m (λ e → m≢k (≡.sym e))

------------------------------------------------------------------------
-- One conjugation step

record Step (g : Gen n) : Set where
  field
    x y   : Fin n
    xy    : x < y
    adj   : toℕ y ≡ suc (toℕ x)
    g′    : Gen n
    small : size g′ ℕ.< size g
    y≤    : y ≤ top g
    top≤  : top g′ ≤ top g
    rel   : [ g ]ʷ ≈ X x y xy • [ g′ ]ʷ • X x y xy

decompose : (g : Gen n) → Basic g ⊎ Step g
decompose (M-gen a) with toℕ a ℕP.≟ 0
... | yes e = inj₁ e
... | no ne = inj₂ record
  { x = x ; y = a ; xy = xa ; adj = ≡.sym (toℕ-predF a h) ; g′ = M-gen x ; small = xa
  ; y≤ = FinP.≤-refl ; top≤ = ℕP.<⇒≤ xa ; rel = conj (X-gen x a xa) (axiom (r3c xa)) }
  where
  h = ℕP.n≢0⇒n>0 ne
  x = predF a h
  xa = predF< a h
decompose (X-gen a b p) with toℕ b ℕP.≟ suc (toℕ a)
... | yes e = inj₁ e
... | no ne = inj₂ record
  { x = a ; y = a′ ; xy = aa′ ; adj = toℕ-sucF a b h ; g′ = X-gen a′ b a′b
  ; small = ≡.subst (λ m → toℕ b ∸ m ℕ.< toℕ b ∸ toℕ a) (≡.sym (toℕ-sucF a b h)) (∸-suc< (toℕ a) (toℕ b) (rc p))
  ; y≤ = ℕP.<⇒≤ a′b ; top≤ = FinP.≤-refl
  ; rel = conj (X-gen a a′ aa′) (axiom (r3a aa′ a′b p)) }
  where
  h : suc (toℕ a) ℕ.< toℕ b
  h = pos (λ e → ne e) (rc p)
  a′ = sucF a b h
  aa′ : a < a′
  aa′ = ≡.subst (toℕ a ℕ.<_) (≡.sym (toℕ-sucF a b h)) (ℕP.n<1+n _)
  a′b : a′ < b
  a′b = ≡.subst (ℕ._< toℕ b) (≡.sym (toℕ-sucF a b h)) h
decompose (K-gen a b c d p q r) with toℕ a ℕP.≟ 0
... | no ne = inj₂ record
  { x = x ; y = a ; xy = xa ; adj = ≡.sym (toℕ-predF a h) ; g′ = K-gen x b c d xb q r
  ; small = ℕP.+-monoˡ-< (toℕ d) (ℕP.+-monoˡ-< (toℕ c) (ℕP.+-monoˡ-< (toℕ b) xa))
  ; y≤ = ℕP.<⇒≤ (FinP.<-trans (rc p) (FinP.<-trans (rc q) (rc r))) ; top≤ = FinP.≤-refl
  ; rel = conj′ (X-gen x a xa) (axiom (r3d xa p q r xb)) }
  where
  h = ℕP.n≢0⇒n>0 ne
  x = predF a h
  xa = predF< a h
  xb = FinP.<-trans xa (rc p)
... | yes a0 with toℕ b ℕP.≟ 1
...   | no ne = inj₂ record
  { x = x ; y = b ; xy = xb ; adj = ≡.sym (toℕ-predF b hb) ; g′ = K-gen a x c d ax xc r
  ; small = ℕP.+-monoˡ-< (toℕ d) (ℕP.+-monoˡ-< (toℕ c) (ℕP.+-monoʳ-< (toℕ a) xb))
  ; y≤ = ℕP.<⇒≤ (FinP.<-trans (rc q) (rc r)) ; top≤ = FinP.≤-refl
  ; rel = conj′ (X-gen x b xb) (axiom (r3e ax xb q r xc p)) }
  where
  hb : 0 ℕ.< toℕ b
  hb = ℕP.≤-<-trans ℕ.z≤n (rc p)
  x = predF b hb
  xb = predF< b hb
  xc = FinP.<-trans xb (rc q)
  -- a = 0 < x, as b > 1.
  ax : a < x
  ax = ≡.subst (ℕ._< toℕ x) (≡.sym a0)
         (ℕP.≤-<-trans ℕ.z≤n (ℕP.≤∧≢⇒< ℕ.z≤n (λ e → ne (≡.trans (≡.sym (toℕ-predF b hb)) (≡.cong suc (≡.sym e))))))
...   | yes b1 with toℕ c ℕP.≟ 2
...     | no ne = inj₂ record
  { x = x ; y = c ; xy = xc ; adj = ≡.sym (toℕ-predF c hc) ; g′ = K-gen a b x d p bx xd
  ; small = ℕP.+-monoˡ-< (toℕ d) (ℕP.+-monoʳ-< (toℕ a ℕ.+ toℕ b) xc)
  ; y≤ = ℕP.<⇒≤ (rc r) ; top≤ = FinP.≤-refl
  ; rel = conj′ (X-gen x c xc) (axiom (r3f p bx xc r xd q)) }
  where
  hc : 0 ℕ.< toℕ c
  hc = ℕP.≤-<-trans ℕ.z≤n (FinP.<-trans (rc p) (rc q))
  x = predF c hc
  xc = predF< c hc
  xd = FinP.<-trans xc (rc r)
  -- b = 1 < x, as c > 2.
  bx : b < x
  bx = ≡.subst (ℕ._< toℕ x) (≡.sym b1)
         (ℕP.≤∧≢⇒< (ℕP.≤-pred (≡.subst (2 ℕ.≤_) (≡.sym (toℕ-predF c hc))
                                   (≡.subst (ℕ._< toℕ c) b1 (rc q))))
                   (λ e → ne (≡.trans (≡.sym (toℕ-predF c hc)) (≡.cong suc (≡.sym e)))))
...     | yes c2 with toℕ d ℕP.≟ 3
...       | yes d3 = inj₁ (a0 , b1 , c2 , d3)
...       | no ne = inj₂ record
  { x = x ; y = d ; xy = xd ; adj = ≡.sym (toℕ-predF d hd) ; g′ = K-gen a b c x p q cx
  ; small = ℕP.+-monoʳ-< (toℕ a ℕ.+ toℕ b ℕ.+ toℕ c) xd
  ; y≤ = FinP.≤-refl ; top≤ = ℕP.<⇒≤ xd
  ; rel = conj′ (X-gen x d xd) (axiom (r3g p q cx xd r)) }
  where
  hd : 0 ℕ.< toℕ d
  hd = ℕP.≤-<-trans ℕ.z≤n (FinP.<-trans (rc p) (FinP.<-trans (rc q) (rc r)))
  x = predF d hd
  xd = predF< d hd
  -- c = 2 < x, as d > 3.
  cx : c < x
  cx = ≡.subst (ℕ._< toℕ x) (≡.sym c2)
         (ℕP.≤∧≢⇒< (ℕP.≤-pred (≡.subst (3 ℕ.≤_) (≡.sym (toℕ-predF d hd))
                                   (≡.subst (ℕ._< toℕ d) c2 (rc r))))
                   (λ e → ne (≡.trans (≡.sym (toℕ-predF d hd)) (≡.cong suc (≡.sym e)))))

------------------------------------------------------------------------
-- All edges from the basic edges

-- The basic edges out of the states at L that do not go up.
BasicAt : Lvl → Set
BasicAt L = ∀ (b : Gen n) (M : Matrix n n D) .(o : ColOrth M) → Basic b →
            level M ≡ L → level (actM b M) ≤ₗ L → Path [ b ]ʷ M o

module Edges {L : Lvl} (ih : EdgesBelow L) (basicAt : BasicAt L) {p : Fin n} (bp : Bℓ p ≤ₗ L) where

  -- A basic edge between states at most at L.
  basic-edge : ∀ (b : Gen n) (s : Matrix n n D) .(o : ColOrth s) → Basic b →
               level s ≤ₗ L → level (actM b s) ≤ₗ L → Path [ b ]ʷ s o
  basic-edge b s o B (inj₂ eq) le = basicAt b s o B eq le
  basic-edge b s o B (inj₁ lt) (inj₁ lt′) = ih b s o lt lt′
  basic-edge b s o B (inj₁ lt) (inj₂ eq) =
    back b s o (basicAt b (actM b s) (ColOrth-actMʷ [ b ]ʷ o) B eq
                  (inj₁ (≡.subst (_<ₗ L) (≡.sym (≡.cong level (act-gg b s))) lt)))

  private
    -- An adjacent X below p keeps a state at most at L.
    X-le : ∀ {x y : Fin n} .(xy : x < y) → y ≤ p → (s : Matrix n n D) → level s ≤ₗ L →
           level (actM (X-gen x y xy) s) ≤ₗ L
    X-le xy y≤p s ls = mono-level-≤ (X-gen _ _ xy) tt y≤p s ls bp

    aux : ∀ k (g : Gen n) → size g ℕ.< k → (s : Matrix n n D) .(o : ColOrth s) → top g ≤ p →
          level s ≤ₗ L → level (actM g s) ≤ₗ L → Path [ g ]ʷ s o
    aux zero g () s o tg ls lgs
    aux (suc k) g sz s o tg ls lgs = by (decompose g)
      where
      by : Basic g ⊎ Step g → Path [ g ]ʷ s o
      by (inj₁ B) = basic-edge g s o B ls lgs
      by (inj₂ st) = path-cong (sym rel) s o
        (path-• Xw (g′w • Xw) s o pX₂ (path-• g′w Xw s o pg′ pX₁))
        where
        open Step st
        Xg = X-gen x y xy
        Xw = [ Xg ]ʷ
        g′w = [ g′ ]ʷ
        y≤p = ℕP.≤-trans y≤ tg
        -- The states along X g′ X.
        s₁ = actM Xg s
        s₂ = actM g′ s₁
        -- g′ X s = X g s.
        s₂≡ : s₂ ≡ actM Xg (actM g s)
        s₂≡ = ≡.trans (≡.sym (act-gg Xg s₂)) (≡.cong (actM Xg) (≡.sym (sound-act rel s)))
        ls₁ : level s₁ ≤ₗ L
        ls₁ = X-le xy y≤p s ls
        ls₂ : level s₂ ≤ₗ L
        ls₂ = ≡.subst (_≤ₗ L) (≡.cong level (≡.sym s₂≡)) (X-le xy y≤p (actM g s) lgs)
        ls₃ : level (actM Xg s₂) ≤ₗ L
        ls₃ = ≡.subst (_≤ₗ L) (≡.cong level (≡.trans (≡.sym (act-gg Xg (actM g s))) (≡.cong (actM Xg) (≡.sym s₂≡)))) lgs
        pX₁ : Path Xw s o
        pX₁ = basic-edge Xg s o adj ls ls₁
        pg′ : Path g′w s₁ (ColOrth-actMʷ Xw o)
        pg′ = aux k g′ (ℕP.<-≤-trans small (ℕP.≤-pred sz)) s₁ (ColOrth-actMʷ Xw o) (ℕP.≤-trans top≤ tg) ls₁ ls₂
        pX₂ : Path Xw s₂ (ColOrth-actMʷ (g′w • Xw) o)
        pX₂ = basic-edge Xg s₂ (ColOrth-actMʷ (g′w • Xw) o) adj ls₂ ls₃

  -- Every edge between states at most at L, of a generator below p.
  edges≤ : ∀ (g : Gen n) (s : Matrix n n D) .(o : ColOrth s) → top g ≤ p →
           level s ≤ₗ L → level (actM g s) ≤ₗ L → Path [ g ]ʷ s o
  edges≤ g = aux (suc (size g)) g (ℕP.n<1+n (size g))
