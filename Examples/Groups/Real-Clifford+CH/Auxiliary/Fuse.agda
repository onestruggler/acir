------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 10's (71), for any six indices
--
--     (H_[a,b] H_[c,d]) (H_[c,d] H_[e,f])  ≈  H_[a,b] H_[e,f]
--
-- `Eq71` proves it where the six are distinct.  The figure states it
-- with no side condition at all, and the degenerate cases are what
-- Item (a)'s Hadamard obligation needs, since its middle pair is the
-- fixed 0, 1.
--
-- The route here is not the paper's.  Where it conjugates a
-- degenerate configuration by a signed permutation built for the
-- purpose, three facts suffice:
--
--   * a letter squares to ε — (65) at its tuple, then (41) and
--     Corollary A.5 cancel from the inside out (`hh-invol`);
--   * hence a letter and its reverse cancel, by (66) (`hh-cancel`);
--   * so the middle pair of a product of two letters may be replaced
--     by any pair fresh to the four outer indices (`hub`): insert the
--     cancelling pair, re-bracket, and the six-index case applies to
--     each half.
--
-- With `hub`, (42) — which splits a *degenerate* letter over the two
-- smallest naturals it misses — reaches every configuration: the
-- middle pair is moved onto those two, in one hop where they are
-- disjoint from it and in two through a fresh pair otherwise.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; _∧_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List ; [] ; _∷_ ; length)
open import Data.Nat using (_<_ ; _≤_ ; s≤s ; z≤n ; _≡ᵇ_) renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; <⇒≢)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (8≤2^)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
  using (_P,_===_ ; r41 ; r42)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (hh ; hhℕ ; distinct4 ; twoSmallest)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (fin ; fin-toℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (hhℕ-hh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m as E65 using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m as F10
  using (Eq65)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq71 m as E71 using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Sigma using (≡ᵇ-t)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Small as SM
  using (small ; module Small)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Avoid as AV
  using (avoid ; module Two ; here ; there)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP (₃₊ m))

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

  -- A numeral below eight is an index at every width.
  lt8 : ∀ {v : ℕ} → v < 8 → v < N
  lt8 p = ≤-trans p (8≤2^ m)

  ≢ℕ : ∀ {x y : Fin N} → toℕ x ≢ toℕ y → x ≢ y
  ≢ℕ ne e = ne (Eq.cong toℕ e)

  -- A conjunction ending in `false`, at the depths `distinct4` needs.
  ∧-z₁ : ∀ (x : Bool) → (x ∧ false) ≡ false
  ∧-z₁ true  = Eq.refl
  ∧-z₁ false = Eq.refl

  ∧-z₂ : ∀ (x y : Bool) → (x ∧ (y ∧ false)) ≡ false
  ∧-z₂ x y = Eq.trans (Eq.cong (x ∧_) (∧-z₁ y)) (∧-z₁ x)

  ∧-z₃ : ∀ (x y z : Bool) → (x ∧ (y ∧ (z ∧ false))) ≡ false
  ∧-z₃ x y z = Eq.trans (Eq.cong (x ∧_) (∧-z₂ y z)) (∧-z₁ x)

  ∧-z₄ : ∀ (x y z w : Bool) → (x ∧ (y ∧ (z ∧ (w ∧ false)))) ≡ false
  ∧-z₄ x y z w = Eq.trans (Eq.cong (x ∧_) (∧-z₃ y z w)) (∧-z₁ x)

  -- Four indices with a repeat among the two pairs are not distinct.
  d4-false : ∀ (A B E F : ℕ) → (A ≡ E) ⊎ (A ≡ F) ⊎ (B ≡ E) ⊎ (B ≡ F) →
             distinct4 A B E F ≡ false
  d4-false A B E F (inj₁ q)
    rewrite ≡ᵇ-t A E q = ∧-z₁ (not (A ≡ᵇ B))
  d4-false A B E F (inj₂ (inj₁ q))
    rewrite ≡ᵇ-t A F q = ∧-z₂ (not (A ≡ᵇ B)) (not (A ≡ᵇ E))
  d4-false A B E F (inj₂ (inj₂ (inj₁ q)))
    rewrite ≡ᵇ-t B E q = ∧-z₃ (not (A ≡ᵇ B)) (not (A ≡ᵇ E)) (not (A ≡ᵇ F))
  d4-false A B E F (inj₂ (inj₂ (inj₂ q)))
    rewrite ≡ᵇ-t B F q =
      ∧-z₄ (not (A ≡ᵇ B)) (not (A ≡ᵇ E)) (not (A ≡ᵇ F)) (not (B ≡ᵇ E))

------------------------------------------------------------------------
-- Two pairs that miss one another

record Off (x y u v : Fin N) : Set where
  constructor mkOff
  field
    xu : x ≢ u
    xv : x ≢ v
    yu : y ≢ u
    yv : y ≢ v

open Off public

off-sym : ∀ {x y u v : Fin N} → Off x y u v → Off u v x y
off-sym o = mkOff (≢sym (xu o)) (≢sym (yu o)) (≢sym (xv o)) (≢sym (yv o))

------------------------------------------------------------------------
-- A three-element cover of four indices that repeat
--
-- Where two of the four coincide, three of them already block
-- everything the four do — which is what keeps the blocked list for
-- `Avoid` down to the six values it can take.

record Cov (x y u v : Fin N) : Set where
  field
    r s t : Fin N
    out : ∀ {z : Fin N} → z ≢ r → z ≢ s → z ≢ t →
          (z ≢ x) × (z ≢ y) × (z ≢ u) × (z ≢ v)

cov : ∀ (x y u v : Fin N) →
      (x ≡ u) ⊎ (x ≡ v) ⊎ (y ≡ u) ⊎ (y ≡ v) → Cov x y u v
cov x y u v (inj₁ e) = record
  { r = x ; s = y ; t = v
  ; out = λ zx zy zv → zx , zy , (λ q → zx (Eq.trans q (Eq.sym e))) , zv }
cov x y u v (inj₂ (inj₁ e)) = record
  { r = x ; s = y ; t = u
  ; out = λ zx zy zu → zx , zy , zu , (λ q → zx (Eq.trans q (Eq.sym e))) }
cov x y u v (inj₂ (inj₂ (inj₁ e))) = record
  { r = x ; s = y ; t = v
  ; out = λ zx zy zv → zx , zy , (λ q → zy (Eq.trans q (Eq.sym e))) , zv }
cov x y u v (inj₂ (inj₂ (inj₂ e))) = record
  { r = x ; s = y ; t = u
  ; out = λ zx zy zu → zx , zy , zu , (λ q → zy (Eq.trans q (Eq.sym e))) }

------------------------------------------------------------------------
-- Everything below is over Equation (65)

module _ (e65 : Eq65) where

  ----------------------------------------------------------------------
  -- A Hadamard letter squares to ε
  --
  -- The inner Σ′Σ cancels, the two standard pairs cancel by (41), and
  -- the outer ΣΣ′ cancels — the same chain `Figure10` runs for (70),
  -- here at an arbitrary tuple.

  hh-invol : ∀ (a b c d : Fin N) →
             a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
             hh {₃₊ m} a b c d • hh {₃₊ m} a b c d ≈ ε
  hh-invol a b c d ab ac ad bc bd cd =
    trans (cong split split) cancel
    where
    module T = E65.Tuple a b c d ab ac ad bc bd cd

    split : hh {₃₊ m} a b c d ≈ T.Σw • (Λ • T.Σ′w)
    split = e65 a b c d ab ac ad bc bd cd

    cancel : (T.Σw • (Λ • T.Σ′w)) • (T.Σw • (Λ • T.Σ′w)) ≈ ε
    cancel = begin
      (T.Σw • (Λ • T.Σ′w)) • (T.Σw • (Λ • T.Σ′w))
        ≈⟨ assoc ⟩
      T.Σw • ((Λ • T.Σ′w) • (T.Σw • (Λ • T.Σ′w)))
        ≈⟨ back T.Σw assoc ⟩
      T.Σw • (Λ • (T.Σ′w • (T.Σw • (Λ • T.Σ′w))))
        ≈⟨ back T.Σw (back Λ (sym assoc)) ⟩
      T.Σw • (Λ • ((T.Σ′w • T.Σw) • (Λ • T.Σ′w)))
        ≈⟨ back T.Σw (back Λ (front (Λ • T.Σ′w) T.Σ′Σ-≈)) ⟩
      T.Σw • (Λ • (ε • (Λ • T.Σ′w)))
        ≈⟨ back T.Σw (back Λ left-unit) ⟩
      T.Σw • (Λ • (Λ • T.Σ′w))
        ≈⟨ back T.Σw (sym assoc) ⟩
      T.Σw • ((Λ • Λ) • T.Σ′w)
        ≈⟨ back T.Σw (front T.Σ′w (axiom r41)) ⟩
      T.Σw • (ε • T.Σ′w)
        ≈⟨ back T.Σw left-unit ⟩
      T.Σw • T.Σ′w
        ≈⟨ T.ΣΣ′-≈ ⟩
      ε ∎

  -- So a letter and its reverse cancel: (66) turns one into the other.
  hh-cancel : ∀ (a b c d : Fin N) →
              a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
              hh {₃₊ m} a b c d • hh {₃₊ m} c d a b ≈ ε
  hh-cancel a b c d ab ac ad bc bd cd =
    trans (back (hh {₃₊ m} a b c d)
                (sym (F10.eq66 e65 a b c d ab ac ad bc bd cd)))
          (hh-invol a b c d ab ac ad bc bd cd)

  ----------------------------------------------------------------------
  -- Changing the middle pair

  hub : ∀ (a b e f c d p q : Fin N) →
        a ≢ b → e ≢ f → c ≢ d → p ≢ q →
        Off a b c d → Off a b p q → Off c d p q → Off c d e f → Off p q e f →
        hh {₃₊ m} a b c d • hh {₃₊ m} c d e f
        ≈ hh {₃₊ m} a b p q • hh {₃₊ m} p q e f
  hub a b e f c d p q ab ef cd pq abcd abpq cdpq cdef pqef = begin
    hh {₃₊ m} a b c d • hh {₃₊ m} c d e f
      ≈⟨ cong left right ⟩
    (hh {₃₊ m} a b p q • hh {₃₊ m} p q c d)
      • (hh {₃₊ m} c d p q • hh {₃₊ m} p q e f)
      ≈⟨ assoc ⟩
    hh {₃₊ m} a b p q • (hh {₃₊ m} p q c d
      • (hh {₃₊ m} c d p q • hh {₃₊ m} p q e f))
      ≈⟨ back (hh {₃₊ m} a b p q) (sym assoc) ⟩
    hh {₃₊ m} a b p q • ((hh {₃₊ m} p q c d • hh {₃₊ m} c d p q)
      • hh {₃₊ m} p q e f)
      ≈⟨ back (hh {₃₊ m} a b p q) (front (hh {₃₊ m} p q e f) inner) ⟩
    hh {₃₊ m} a b p q • (ε • hh {₃₊ m} p q e f)
      ≈⟨ back (hh {₃₊ m} a b p q) left-unit ⟩
    hh {₃₊ m} a b p q • hh {₃₊ m} p q e f ∎
    where
    left : hh {₃₊ m} a b c d ≈ hh {₃₊ m} a b p q • hh {₃₊ m} p q c d
    left = sym (E71.eq71 e65 a b p q c d
                  ab (xu abpq) (xv abpq) (xu abcd) (xv abcd)
                  (yu abpq) (yv abpq) (yu abcd) (yv abcd)
                  pq (≢sym (xu cdpq)) (≢sym (yu cdpq))
                  (≢sym (xv cdpq)) (≢sym (yv cdpq)) cd)

    right : hh {₃₊ m} c d e f ≈ hh {₃₊ m} c d p q • hh {₃₊ m} p q e f
    right = sym (E71.eq71 e65 c d p q e f
                   cd (xu cdpq) (xv cdpq) (xu cdef) (xv cdef)
                   (yu cdpq) (yv cdpq) (yu cdef) (yv cdef)
                   pq (xu pqef) (xv pqef) (yu pqef) (yv pqef) ef)

    inner : hh {₃₊ m} p q c d • hh {₃₊ m} c d p q ≈ ε
    inner = hh-cancel p q c d pq (≢sym (xu cdpq)) (≢sym (yu cdpq))
                    (≢sym (xv cdpq)) (≢sym (yv cdpq)) cd

  ----------------------------------------------------------------------
  -- (71) where the middle pair is fresh to the four outer indices
  --
  -- Where the outer four are distinct this is the six-index case.
  -- Where they are not, (42) splits the right-hand side over the two
  -- smallest naturals they miss, and `hub` carries the middle pair
  -- onto those — directly if it misses them, and through a pair fresh
  -- to everything otherwise, which is where `Avoid` and the covers
  -- come in.

  fuse-fresh : ∀ (a b e f c d : Fin N) → a ≢ b → e ≢ f → c ≢ d →
               Off a b c d → Off c d e f →
               hh {₃₊ m} a b c d • hh {₃₊ m} c d e f ≈ hh {₃₊ m} a b e f
  fuse-fresh a b e f c d ab ef cd abcd cdef =
    go (a ≟ᶠ e) (a ≟ᶠ f) (b ≟ᶠ e) (b ≟ᶠ f)
    where
    Goal : Set
    Goal = hh {₃₊ m} a b c d • hh {₃₊ m} c d e f ≈ hh {₃₊ m} a b e f

    A B E F : ℕ
    A = toℕ a
    B = toℕ b
    E = toℕ e
    F = toℕ f

    -- The two smallest naturals the four outer indices miss.
    module S = Small (small A B E F)

    i′ j′ : Fin N
    i′ = fin S.e (lt8 S.e<8)
    j′ = fin S.f (lt8 S.f<8)

    ti : toℕ i′ ≡ S.e
    ti = fin-toℕ S.e (lt8 S.e<8)

    tj : toℕ j′ ≡ S.f
    tj = fin-toℕ S.f (lt8 S.f<8)

    offI : ∀ (x : Fin N) → S.e ≢ toℕ x → i′ ≢ x
    offI x ne q = ne (Eq.trans (Eq.sym ti) (Eq.cong toℕ q))

    offJ : ∀ (x : Fin N) → S.f ≢ toℕ x → j′ ≢ x
    offJ x ne q = ne (Eq.trans (Eq.sym tj) (Eq.cong toℕ q))

    ij : i′ ≢ j′
    ij q = <⇒≢ S.e<f (Eq.trans (Eq.sym ti) (Eq.trans (Eq.cong toℕ q) tj))

    abij : Off a b i′ j′
    abij = mkOff (≢sym (offI a S.ea)) (≢sym (offJ a S.fa))
                 (≢sym (offI b S.eb)) (≢sym (offJ b S.fb))

    ijef : Off i′ j′ e f
    ijef = mkOff (offI e S.ec) (offI f S.ed) (offJ e S.fc) (offJ f S.fd)

    -- Equation (42) at the four outer indices.
    split : distinct4 A B E F ≡ false →
            hh {₃₊ m} a b i′ j′ • hh {₃₊ m} i′ j′ e f ≈ hh {₃₊ m} a b e f
    split nd = trans (refl≡ (Eq.sym conv)) (axiom (r42 a b e f ab ef nd))
      where
      half₁ : hhℕ {₃₊ m} A B S.e S.f ≡ hh {₃₊ m} a b i′ j′
      half₁ = Eq.trans (Eq.cong₂ (hhℕ {₃₊ m} A B) (Eq.sym ti) (Eq.sym tj))
                       (hhℕ-hh a b i′ j′)

      half₂ : hhℕ {₃₊ m} S.e S.f E F ≡ hh {₃₊ m} i′ j′ e f
      half₂ = Eq.trans (Eq.cong₂ (λ u v → hhℕ {₃₊ m} u v E F)
                                 (Eq.sym ti) (Eq.sym tj))
                       (hhℕ-hh i′ j′ e f)

      conv : hhℕ {₃₊ m} A B (proj₁ (twoSmallest A B E F))
                           (proj₂ (twoSmallest A B E F))
             • hhℕ {₃₊ m} (proj₁ (twoSmallest A B E F))
                          (proj₂ (twoSmallest A B E F)) E F
             ≡ hh {₃₊ m} a b i′ j′ • hh {₃₊ m} i′ j′ e f
      conv = Eq.trans
        (Eq.cong (λ pr → hhℕ {₃₊ m} A B (proj₁ pr) (proj₂ pr)
                       • hhℕ {₃₊ m} (proj₁ pr) (proj₂ pr) E F) S.ts)
        (Eq.cong₂ _•_ half₁ half₂)

    ----------------------------------------------------------------
    -- The degenerate branch

    degen : (a ≡ e) ⊎ (a ≡ f) ⊎ (b ≡ e) ⊎ (b ≡ f) → Goal
    degen h = trans (goHub (c ≟ᶠ i′) (c ≟ᶠ j′) (d ≟ᶠ i′) (d ≟ᶠ j′)) (split nd)
      where
      ndOf : (a ≡ e) ⊎ (a ≡ f) ⊎ (b ≡ e) ⊎ (b ≡ f) →
             (A ≡ E) ⊎ (A ≡ F) ⊎ (B ≡ E) ⊎ (B ≡ F)
      ndOf (inj₁ q)               = inj₁ (Eq.cong toℕ q)
      ndOf (inj₂ (inj₁ q))        = inj₂ (inj₁ (Eq.cong toℕ q))
      ndOf (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₂ (inj₁ (Eq.cong toℕ q)))
      ndOf (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₂ (Eq.cong toℕ q)))

      nd : distinct4 A B E F ≡ false
      nd = d4-false A B E F (ndOf h)

      Mid : Set
      Mid = hh {₃₊ m} a b c d • hh {₃₊ m} c d e f
            ≈ hh {₃₊ m} a b i′ j′ • hh {₃₊ m} i′ j′ e f

      -- Where both configurations repeat, three indices cover each,
      -- and `Avoid` finds a pair fresh to all of them.
      two : (c ≡ i′) ⊎ (c ≡ j′) ⊎ (d ≡ i′) ⊎ (d ≡ j′) → Mid
      two k = trans (hub a b e f c d p′ q′ ab ef cd pq abcd abpq cdpq cdef pqef)
                    (hub a b e f p′ q′ i′ j′ ab ef pq ij abpq abij pqij
                         pqef ijef)
        where
        module C₁ = Cov (cov a b e f h)
        module C₂ = Cov (cov c d i′ j′ k)

        bs : List ℕ
        bs = toℕ C₁.r ∷ toℕ C₁.s ∷ toℕ C₁.t
           ∷ toℕ C₂.r ∷ toℕ C₂.s ∷ toℕ C₂.t ∷ []

        module T = Two (avoid bs ≤-refl)

        p′ q′ : Fin N
        p′ = fin T.p (lt8 T.p<)
        q′ = fin T.q (lt8 T.q<)

        tp : toℕ p′ ≡ T.p
        tp = fin-toℕ T.p (lt8 T.p<)

        tq : toℕ q′ ≡ T.q
        tq = fin-toℕ T.q (lt8 T.q<)

        offP : ∀ (x : Fin N) → T.p ≢ toℕ x → p′ ≢ x
        offP x ne r = ne (Eq.trans (Eq.sym tp) (Eq.cong toℕ r))

        offQ : ∀ (x : Fin N) → T.q ≢ toℕ x → q′ ≢ x
        offQ x ne r = ne (Eq.trans (Eq.sym tq) (Eq.cong toℕ r))

        -- What the fresh pair misses, read off the two covers.
        P₁ : (p′ ≢ a) × (p′ ≢ b) × (p′ ≢ e) × (p′ ≢ f)
        P₁ = C₁.out (offP C₁.r (T.p∉ here)) (offP C₁.s (T.p∉ (there here)))
                    (offP C₁.t (T.p∉ (there (there here))))

        P₂ : (p′ ≢ c) × (p′ ≢ d) × (p′ ≢ i′) × (p′ ≢ j′)
        P₂ = C₂.out (offP C₂.r (T.p∉ (there (there (there here)))))
                    (offP C₂.s (T.p∉ (there (there (there (there here))))))
                    (offP C₂.t
                      (T.p∉ (there (there (there (there (there here)))))))

        Q₁ : (q′ ≢ a) × (q′ ≢ b) × (q′ ≢ e) × (q′ ≢ f)
        Q₁ = C₁.out (offQ C₁.r (T.q∉ here)) (offQ C₁.s (T.q∉ (there here)))
                    (offQ C₁.t (T.q∉ (there (there here))))

        Q₂ : (q′ ≢ c) × (q′ ≢ d) × (q′ ≢ i′) × (q′ ≢ j′)
        Q₂ = C₂.out (offQ C₂.r (T.q∉ (there (there (there here)))))
                    (offQ C₂.s (T.q∉ (there (there (there (there here))))))
                    (offQ C₂.t
                      (T.q∉ (there (there (there (there (there here)))))))

        pq : p′ ≢ q′
        pq r = T.p≢q (Eq.trans (Eq.sym tp) (Eq.trans (Eq.cong toℕ r) tq))

        abpq : Off a b p′ q′
        abpq = mkOff (≢sym (proj₁ P₁)) (≢sym (proj₁ Q₁))
                     (≢sym (proj₁ (proj₂ P₁))) (≢sym (proj₁ (proj₂ Q₁)))

        cdpq : Off c d p′ q′
        cdpq = mkOff (≢sym (proj₁ P₂)) (≢sym (proj₁ Q₂))
                     (≢sym (proj₁ (proj₂ P₂))) (≢sym (proj₁ (proj₂ Q₂)))

        pqef : Off p′ q′ e f
        pqef = mkOff (proj₁ (proj₂ (proj₂ P₁))) (proj₂ (proj₂ (proj₂ P₁)))
                     (proj₁ (proj₂ (proj₂ Q₁))) (proj₂ (proj₂ (proj₂ Q₁)))

        pqij : Off p′ q′ i′ j′
        pqij = mkOff (proj₁ (proj₂ (proj₂ P₂))) (proj₂ (proj₂ (proj₂ P₂)))
                     (proj₁ (proj₂ (proj₂ Q₂))) (proj₂ (proj₂ (proj₂ Q₂)))

      -- Where the middle pair already misses those two, one hop.
      goHub : Dec (c ≡ i′) → Dec (c ≡ j′) → Dec (d ≡ i′) → Dec (d ≡ j′) → Mid
      goHub (yes q) _ _ _ = two (inj₁ q)
      goHub _ (yes q) _ _ = two (inj₂ (inj₁ q))
      goHub _ _ (yes q) _ = two (inj₂ (inj₂ (inj₁ q)))
      goHub _ _ _ (yes q) = two (inj₂ (inj₂ (inj₂ q)))
      goHub (no ci) (no cj) (no di) (no dj) =
        hub a b e f c d i′ j′ ab ef cd ij abcd abij (mkOff ci cj di dj)
            cdef ijef

    ----------------------------------------------------------------
    -- And the main branch is the six-index case

    go : Dec (a ≡ e) → Dec (a ≡ f) → Dec (b ≡ e) → Dec (b ≡ f) → Goal
    go (yes q) _ _ _ = degen (inj₁ q)
    go _ (yes q) _ _ = degen (inj₂ (inj₁ q))
    go _ _ (yes q) _ = degen (inj₂ (inj₂ (inj₁ q)))
    go _ _ _ (yes q) = degen (inj₂ (inj₂ (inj₂ q)))
    go (no ae) (no af) (no be) (no bf) =
      E71.eq71 e65 a b c d e f ab (xu abcd) (xv abcd) ae af
               (yu abcd) (yv abcd) be bf cd (xu cdef) (xv cdef)
               (yu cdef) (yv cdef) ef

  ----------------------------------------------------------------------
  -- Equation (71), for any six indices
  --
  -- A pair fresh to all six splits both letters, the two inner halves
  -- cancel, and what is left is the fresh-middle case again.

  fuse : ∀ (a b c d e f : Fin N) → a ≢ b → c ≢ d → e ≢ f →
         hh {₃₊ m} a b c d • hh {₃₊ m} c d e f ≈ hh {₃₊ m} a b e f
  fuse a b c d e f ab cd ef = begin
    hh {₃₊ m} a b c d • hh {₃₊ m} c d e f
      ≈⟨ cong left right ⟩
    (hh {₃₊ m} a b p′ q′ • hh {₃₊ m} p′ q′ c d)
      • (hh {₃₊ m} c d p′ q′ • hh {₃₊ m} p′ q′ e f)
      ≈⟨ assoc ⟩
    hh {₃₊ m} a b p′ q′ • (hh {₃₊ m} p′ q′ c d
      • (hh {₃₊ m} c d p′ q′ • hh {₃₊ m} p′ q′ e f))
      ≈⟨ back (hh {₃₊ m} a b p′ q′) (sym assoc) ⟩
    hh {₃₊ m} a b p′ q′ • ((hh {₃₊ m} p′ q′ c d • hh {₃₊ m} c d p′ q′)
      • hh {₃₊ m} p′ q′ e f)
      ≈⟨ back (hh {₃₊ m} a b p′ q′) (front (hh {₃₊ m} p′ q′ e f) inner) ⟩
    hh {₃₊ m} a b p′ q′ • (ε • hh {₃₊ m} p′ q′ e f)
      ≈⟨ back (hh {₃₊ m} a b p′ q′) left-unit ⟩
    hh {₃₊ m} a b p′ q′ • hh {₃₊ m} p′ q′ e f
      ≈⟨ fuse-fresh a b e f p′ q′ ab ef pq abpq pqef ⟩
    hh {₃₊ m} a b e f ∎
    where
    bs : List ℕ
    bs = toℕ a ∷ toℕ b ∷ toℕ c ∷ toℕ d ∷ toℕ e ∷ toℕ f ∷ []

    module T = Two (avoid bs ≤-refl)

    p′ q′ : Fin N
    p′ = fin T.p (lt8 T.p<)
    q′ = fin T.q (lt8 T.q<)

    tp : toℕ p′ ≡ T.p
    tp = fin-toℕ T.p (lt8 T.p<)

    tq : toℕ q′ ≡ T.q
    tq = fin-toℕ T.q (lt8 T.q<)

    offP : ∀ (x : Fin N) → T.p ≢ toℕ x → p′ ≢ x
    offP x ne r = ne (Eq.trans (Eq.sym tp) (Eq.cong toℕ r))

    offQ : ∀ (x : Fin N) → T.q ≢ toℕ x → q′ ≢ x
    offQ x ne r = ne (Eq.trans (Eq.sym tq) (Eq.cong toℕ r))

    pq : p′ ≢ q′
    pq r = T.p≢q (Eq.trans (Eq.sym tp) (Eq.trans (Eq.cong toℕ r) tq))

    abpq : Off a b p′ q′
    abpq = mkOff (≢sym (offP a (T.p∉ here))) (≢sym (offQ a (T.q∉ here)))
                 (≢sym (offP b (T.p∉ (there here))))
                 (≢sym (offQ b (T.q∉ (there here))))

    cdpq : Off c d p′ q′
    cdpq = mkOff (≢sym (offP c (T.p∉ (there (there here)))))
                 (≢sym (offQ c (T.q∉ (there (there here)))))
                 (≢sym (offP d (T.p∉ (there (there (there here))))))
                 (≢sym (offQ d (T.q∉ (there (there (there here))))))

    pqef : Off p′ q′ e f
    pqef = mkOff (offP e (T.p∉ (there (there (there (there here))))))
                 (offP f (T.p∉ (there (there (there (there (there here)))))))
                 (offQ e (T.q∉ (there (there (there (there here))))))
                 (offQ f (T.q∉ (there (there (there (there (there here)))))))

    left : hh {₃₊ m} a b c d ≈ hh {₃₊ m} a b p′ q′ • hh {₃₊ m} p′ q′ c d
    left = sym (fuse-fresh a b c d p′ q′ ab cd pq abpq (off-sym cdpq))

    right : hh {₃₊ m} c d e f ≈ hh {₃₊ m} c d p′ q′ • hh {₃₊ m} p′ q′ e f
    right = sym (fuse-fresh c d e f p′ q′ cd ef pq cdpq pqef)

    inner : hh {₃₊ m} p′ q′ c d • hh {₃₊ m} c d p′ q′ ≈ ε
    inner = hh-cancel p′ q′ c d pq (≢sym (xu cdpq)) (≢sym (yu cdpq))
                      (≢sym (xv cdpq)) (≢sym (yv cdpq)) cd

  ----------------------------------------------------------------------
  -- (73): the two inner pairs of a product of two letters exchange
  --
  -- The letters denote H_[a,b] H_[c,d] H_[e,f] H_[g,h], and (73) is
  -- the commutation of the two middle factors.  Split the first letter
  -- over the third pair, turn the pair that is left round by (66), and
  -- fuse the other half back.

  eq73 : ∀ (a b c d e f g h : Fin N) →
         a ≢ b → c ≢ d → e ≢ f → g ≢ h → Off c d e f →
         hh {₃₊ m} a b c d • hh {₃₊ m} e f g h
         ≈ hh {₃₊ m} a b e f • hh {₃₊ m} c d g h
  eq73 a b c d e f g h ab cd ef gh cdef = begin
    hh {₃₊ m} a b c d • hh {₃₊ m} e f g h
      ≈⟨ front (hh {₃₊ m} e f g h) (sym (fuse a b e f c d ab ef cd)) ⟩
    (hh {₃₊ m} a b e f • hh {₃₊ m} e f c d) • hh {₃₊ m} e f g h
      ≈⟨ assoc ⟩
    hh {₃₊ m} a b e f • (hh {₃₊ m} e f c d • hh {₃₊ m} e f g h)
      ≈⟨ back (hh {₃₊ m} a b e f) (front (hh {₃₊ m} e f g h) turn) ⟩
    hh {₃₊ m} a b e f • (hh {₃₊ m} c d e f • hh {₃₊ m} e f g h)
      ≈⟨ back (hh {₃₊ m} a b e f) (fuse c d e f g h cd ef gh) ⟩
    hh {₃₊ m} a b e f • hh {₃₊ m} c d g h ∎
    where
    turn : hh {₃₊ m} e f c d ≈ hh {₃₊ m} c d e f
    turn = F10.eq66 e65 e f c d ef (≢sym (xu cdef)) (≢sym (yu cdef))
                    (≢sym (xv cdef)) (≢sym (yv cdef)) cd
