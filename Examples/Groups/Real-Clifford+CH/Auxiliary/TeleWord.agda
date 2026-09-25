------------------------------------------------------------------------
-- Presentations of groups
--
-- The word a telescope builds
--
-- `Telescope` says what a plan does to the numerals; this module
-- builds the word that does it — one `(−1)_[m] X_[x,i]` letter per
-- step, its exchange the step's own transposition and its sign the
-- image of a *spare* numeral, one the plan does not use.
--
--     wrd s []            = ε
--     wrd s ((x , k) ∷ p) = (−1)_[ρ ((x,k)∷p) s] X_[x , ρ p k] · wrd s p
--
-- Its permutation is the plan's `P`, and it signs no index the plan
-- reaches from a numeral other than the spare one — because the k-th
-- sign sits at `ρ (drop k) s` and the point the k-th letter is reached
-- at is `ρ (drop k) j`, and ρ is injective.
--
-- The companion `wrd′` has the same transpositions in the other order,
-- each carrying the *next* sign up, so the letters pair off by
-- transposition and the product telescopes to ε.
--
-- Definition E.1's own Σ is `wrd 4 [(a,0),(b,1),(c,3),(d,2)]` — the
-- same letters with the same indices, differing only by a trailing ε —
-- and what this is for is the six-index analogue that Figure 10's (71)
-- needs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.TeleWord (m : ℕ) where

open import Data.Bool using (Bool ; false ; _xor_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (_<_) renaming (_^_ to _^ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zx ; zxℕ ; τ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zxℕ-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (fin ; fin-toℕ ; HFreeʷ ; nil ; cat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; idSP ; swapF)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-refl to ≐-refl′ ; ≐-trans to ≐-trans′
          ; ≐-sym to ≐-sym′
          ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′ ; ⊙-idˡ to ⊙-idˡ′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m
  using (zx-prm ; zx-sgn ; hfree-zx ; swapF-τ ; zx-pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Sigma using (τ-invol)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Telescope

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  -- Deciding a letter's three indices.
  lit : ∀ (u x y : ℕ) (pu : u < N) (px : x < N) (py : y < N) →
        zxℕ {₃₊ m} u x y ≡ zx (fin u pu) (fin x px) (fin y py)
  lit u x y pu px py =
    Eq.trans (Eq.cong₂ (λ s t → zxℕ {₃₊ m} s t y)
                       (Eq.sym (fin-toℕ u pu)) (Eq.sym (fin-toℕ x px)))
      (Eq.trans (Eq.cong (zxℕ {₃₊ m} (toℕ (fin u pu)) (toℕ (fin x px)))
                         (Eq.sym (fin-toℕ y py)))
                (zxℕ-zx (fin u pu) (fin x px) (fin y py)))

  sp≡ : ∀ {u v : W} → u ≡ v → sp u ≗ sp v
  sp≡ Eq.refl = ≐-refl′

------------------------------------------------------------------------
-- The two words
--
-- **Abstract**: a plan's word unfolds into a letter per step whose
-- indices are nested transpositions, and anything that reads it — a
-- matrix, a scale, a _~_ — would expand all of that at every
-- comparison.  The equations it is used through are the lemmas below,
-- which live in the same abstract block.

wrd wrd′ : ℕ → Plan → W
wrd  s []             = ε
wrd  s ((x , k) ∷ ys) = zxℕ {₃₊ m} (ρ ((x , k) ∷ ys) s) x (ρ ys k) • wrd s ys
wrd′ s []             = ε
wrd′ s ((x , k) ∷ ys) = wrd′ s ys • zxℕ {₃₊ m} (ρ ys s) x (ρ ys k)

------------------------------------------------------------------------
-- They are Hadamard-free

module _ (s : ℕ) (s< : s < N) where

  hfree : ∀ (xs : Plan) → Bounded N xs → HFreeʷ (wrd s xs)
  hfree []             bd = nil
  hfree ((x , k) ∷ ys) bd =
    Eq.subst HFreeʷ (Eq.sym (Eq.cong (_• wrd s ys) (lit _ _ _ p₀ p₁ p₂)))
      (cat (hfree-zx (fin _ p₀) (fin _ p₁) (fin _ p₂))
           (hfree ys bd′))
    where
    bd′ : Bounded N ys
    bd′ mem = bd (there mem)

    p₀ : ρ ((x , k) ∷ ys) s < N
    p₀ = ρ-< ((x , k) ∷ ys) bd s<

    p₁ : x < N
    p₁ = proj₁ (bd here)

    p₂ : ρ ys k < N
    p₂ = ρ-< ys bd′ (proj₂ (bd here))

  hfree′ : ∀ (xs : Plan) → Bounded N xs → HFreeʷ (wrd′ s xs)
  hfree′ []             bd = nil
  hfree′ ((x , k) ∷ ys) bd =
    Eq.subst HFreeʷ (Eq.sym (Eq.cong (wrd′ s ys •_) (lit _ _ _ q₀ p₁ p₂)))
      (cat (hfree′ ys bd′)
           (hfree-zx (fin _ q₀) (fin _ p₁) (fin _ p₂)))
    where
    bd′ : Bounded N ys
    bd′ mem = bd (there mem)

    q₀ : ρ ys s < N
    q₀ = ρ-< ys bd′ s<

    p₁ : x < N
    p₁ = proj₁ (bd here)

    p₂ : ρ ys k < N
    p₂ = ρ-< ys bd′ (proj₂ (bd here))

  ----------------------------------------------------------------------
  -- Its permutation is the plan's

  prm-wrd : ∀ (xs : Plan) (bd : Bounded N xs) (v : Fin N) →
            toℕ (prm (sp (wrd s xs)) v) ≡ P xs (toℕ v)
  prm-wrd []             bd v = Eq.refl
  prm-wrd ((x , k) ∷ ys) bd v =
    Eq.trans (Eq.cong (λ w → toℕ (prm (sp (w • wrd s ys)) v))
                      (lit _ _ _ p₀ p₁ p₂))
      (Eq.trans (prm-wrd ys bd′ (prm (sp (zx (fin _ p₀) (fin _ p₁) (fin _ p₂))) v))
                (Eq.cong (P ys) step))
    where
    bd′ : Bounded N ys
    bd′ mem = bd (there mem)

    p₀ : ρ ((x , k) ∷ ys) s < N
    p₀ = ρ-< ((x , k) ∷ ys) bd s<

    p₁ : x < N
    p₁ = proj₁ (bd here)

    p₂ : ρ ys k < N
    p₂ = ρ-< ys bd′ (proj₂ (bd here))

    step : toℕ (prm (sp (zx (fin _ p₀) (fin _ p₁) (fin _ p₂))) v)
           ≡ τ x (ρ ys k) (toℕ v)
    step =
      Eq.trans (Eq.cong toℕ (zx-prm (fin _ p₀) (fin _ p₁) (fin _ p₂) v))
        (Eq.trans (swapF-τ (fin _ p₁) (fin _ p₂) v)
                  (Eq.cong₂ (λ a b → τ a b (toℕ v))
                            (fin-toℕ x p₁) (fin-toℕ (ρ ys k) p₂)))

  ----------------------------------------------------------------------
  -- And it signs nothing the plan reaches from another numeral

  sgn-wrd : ∀ (xs : Plan) (bd : Bounded N xs) (j : ℕ) → j ≢ s →
            ∀ (v : Fin N) → toℕ v ≡ ρ xs j →
            sgn (sp (wrd s xs)) v ≡ false
  sgn-wrd []             bd j js v ev = Eq.refl
  sgn-wrd ((x , k) ∷ ys) bd j js v ev =
    Eq.trans (Eq.cong (λ w → sgn (sp (w • wrd s ys)) v) (lit _ _ _ p₀ p₁ p₂))
      (Eq.trans (Eq.cong₂ _xor_ head tail) Eq.refl)
    where
    bd′ : Bounded N ys
    bd′ mem = bd (there mem)

    p₀ : ρ ((x , k) ∷ ys) s < N
    p₀ = ρ-< ((x , k) ∷ ys) bd s<

    p₁ : x < N
    p₁ = proj₁ (bd here)

    p₂ : ρ ys k < N
    p₂ = ρ-< ys bd′ (proj₂ (bd here))

    -- The head letter's own index is the image of the spare numeral,
    -- which is not where v sits.
    head : sgn (sp (zx (fin _ p₀) (fin _ p₁) (fin _ p₂))) v ≡ false
    head = zx-sgn (fin _ p₀) (fin _ p₁) (fin _ p₂) v off
      where
      off : v ≢ fin _ p₀
      off e = js (ρ-inj ((x , k) ∷ ys)
                   (Eq.trans (Eq.sym ev)
                     (Eq.trans (Eq.cong toℕ e) (fin-toℕ _ p₀))))

    -- And the point the tail is reached at is the tail's own image of
    -- the same numeral, the head transposition being an involution.
    next : toℕ (prm (sp (zx (fin _ p₀) (fin _ p₁) (fin _ p₂))) v) ≡ ρ ys j
    next =
      Eq.trans (Eq.cong toℕ (zx-prm (fin _ p₀) (fin _ p₁) (fin _ p₂) v))
        (Eq.trans (swapF-τ (fin _ p₁) (fin _ p₂) v)
          (Eq.trans (Eq.cong₂ (λ a b → τ a b (toℕ v))
                              (fin-toℕ x p₁) (fin-toℕ (ρ ys k) p₂))
            (Eq.trans (Eq.cong (τ x (ρ ys k)) ev)
                      (τ-invol x (ρ ys k) (ρ ys j)))))

    tail : sgn (sp (wrd s ys))
                (prm (sp (zx (fin _ p₀) (fin _ p₁) (fin _ p₂))) v) ≡ false
    tail = sgn-wrd ys bd′ j js _ next

------------------------------------------------------------------------
-- The two words are inverse
--
-- The k-th letter of `wrd` and the k-th of `wrd′` carry the same
-- transposition — so they are the empty word together or not at all —
-- and the first's sign is the second's transposed, which is exactly
-- when a pair of such letters cancels.

module _ (s : ℕ) (s< : s < N) where

  inv : ∀ (xs : Plan) → Bounded N xs →
        sp (wrd s xs) ⊛ sp (wrd′ s xs) ≗ idSP
  inv []             bd = ⊙-idˡ′ idSP
  inv ((x , k) ∷ ys) bd =
    ≐-trans′ (⊙-cong′ (⊙-cong′ (sp≡ (lit _ _ _ p₀ p₁ p₂)) (≐-refl′ {sp (wrd s ys)}))
                      (⊙-cong′ (≐-refl′ {sp (wrd′ s ys)})
                               (sp≡ (lit _ _ _ q₀ p₁ p₂))))
             (peel (sp (zx (fin _ p₀) (fin _ p₁) (fin _ p₂)))
                   (sp (wrd s ys)) (sp (wrd′ s ys))
                   (sp (zx (fin _ q₀) (fin _ p₁) (fin _ p₂)))
                   (inv ys bd′) pair)
    where
    bd′ : Bounded N ys
    bd′ mem = bd (there mem)

    p₀ : ρ ((x , k) ∷ ys) s < N
    p₀ = ρ-< ((x , k) ∷ ys) bd s<

    q₀ : ρ ys s < N
    q₀ = ρ-< ys bd′ s<

    p₁ : x < N
    p₁ = proj₁ (bd here)

    p₂ : ρ ys k < N
    p₂ = ρ-< ys bd′ (proj₂ (bd here))

    -- The head's sign is the tail's sign transposed.
    shift : fin _ p₀ ≡ swapF (fin _ p₁) (fin _ p₂) (fin _ q₀)
    shift = toℕ-injective (Eq.trans (fin-toℕ _ p₀) (Eq.sym other))
      where
      other : toℕ (swapF (fin _ p₁) (fin _ p₂) (fin _ q₀)) ≡ ρ ((x , k) ∷ ys) s
      other =
        Eq.trans (swapF-τ (fin _ p₁) (fin _ p₂) (fin _ q₀))
          (Eq.trans (Eq.cong₂ (λ a b → τ a b (toℕ (fin _ q₀)))
                              (fin-toℕ x p₁) (fin-toℕ (ρ ys k) p₂))
                    (Eq.cong (τ x (ρ ys k)) (fin-toℕ _ q₀)))

    pair : sp (zx (fin _ p₀) (fin _ p₁) (fin _ p₂))
           ⊛ sp (zx (fin _ q₀) (fin _ p₁) (fin _ p₂)) ≗ idSP
    pair = zx-pair (fin _ p₀) (fin _ q₀) (fin _ p₁) (fin _ p₂) shift

    -- (f ⊛ A) ⊛ (B ⊛ g) with A ⊛ B and f ⊛ g both the identity.
    peel : ∀ (f A B g : SP) → (A ⊛ B) ≗ idSP → (f ⊛ g) ≗ idSP →
           (f ⊛ A) ⊛ (B ⊛ g) ≗ idSP
    peel f A B g e e′ =
      ≐-trans′ (⊙-assoc′ f A (B ⊛ g))
      (≐-trans′ (⊙-cong′ (≐-refl′ {f})
                  (≐-trans′ (≐-trans′ (≐-sym′ (⊙-assoc′ A B g))
                                      (⊙-cong′ e (≐-refl′ {g})))
                            (⊙-idˡ′ g)))
                e′)

------------------------------------------------------------------------
-- An opaque alias
--
-- A plan's word unfolds into a letter per step whose indices are
-- nested transpositions, so anything that reads it — a matrix, a
-- scale, a `_~_` — expands all of that at every comparison; two
-- hundred seconds and two gigabytes were not enough for the six-index
-- instance.  Clients use `Wrd`, which is abstract, and the five
-- lemmas below carry everything proved above across.

abstract
  Wrd Wrd′ : ℕ → Plan → W
  Wrd  = wrd
  Wrd′ = wrd′

  Wrd≡ : ∀ (s : ℕ) (xs : Plan) → Wrd s xs ≡ wrd s xs
  Wrd≡ s xs = Eq.refl

  Wrd′≡ : ∀ (s : ℕ) (xs : Plan) → Wrd′ s xs ≡ wrd′ s xs
  Wrd′≡ s xs = Eq.refl

module _ (s : ℕ) (s< : s < N) where

  Hfree : ∀ (xs : Plan) → Bounded N xs → HFreeʷ (Wrd s xs)
  Hfree xs bd = Eq.subst HFreeʷ (Eq.sym (Wrd≡ s xs)) (hfree s s< xs bd)

  Hfree′ : ∀ (xs : Plan) → Bounded N xs → HFreeʷ (Wrd′ s xs)
  Hfree′ xs bd = Eq.subst HFreeʷ (Eq.sym (Wrd′≡ s xs)) (hfree′ s s< xs bd)

  Prm-wrd : ∀ (xs : Plan) (bd : Bounded N xs) (v : Fin N) →
            toℕ (prm (sp (Wrd s xs)) v) ≡ P xs (toℕ v)
  Prm-wrd xs bd v =
    Eq.trans (Eq.cong (λ w → toℕ (prm (sp w) v)) (Wrd≡ s xs))
             (prm-wrd s s< xs bd v)

  Sgn-wrd : ∀ (xs : Plan) (bd : Bounded N xs) (j : ℕ) → j ≢ s →
            ∀ (v : Fin N) → toℕ v ≡ ρ xs j → sgn (sp (Wrd s xs)) v ≡ false
  Sgn-wrd xs bd j js v ev =
    Eq.trans (Eq.cong (λ w → sgn (sp w) v) (Wrd≡ s xs))
             (sgn-wrd s s< xs bd j js v ev)

  Inv : ∀ (xs : Plan) → Bounded N xs → sp (Wrd s xs) ⊛ sp (Wrd′ s xs) ≗ idSP
  Inv xs bd =
    ≐-trans′ (⊙-cong′ (sp≡ (Wrd≡ s xs)) (sp≡ (Wrd′≡ s xs))) (inv s s< xs bd)
