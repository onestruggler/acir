------------------------------------------------------------------------
-- Presentations of groups
--
-- Definition E.1's word, read as a signed permutation
--
-- `Sigma` analyses the four transpositions of Definition E.1 over the
-- natural numbers; this module reads them off the word itself.  The
-- result is what Equation (65) needs of it: its permutation carries
-- a, b, c, d to the indices 0, 1, 3, 2, and it signs none of the four.
--
-- Two things have to be crossed.  The letters are `zxℕ`, which decides
-- `toFin` on each of its three indices, so each is converted once by
-- `zxℕ-zx`; and a letter whose two X-indices coincide is the *empty*
-- word, not a letter — which is harmless here, since an empty letter
-- neither permutes (and neither does the transposition it stands for)
-- nor signs (and a sign that is not there is not a sign at a, b, c
-- or d).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm (m : ℕ) where

open import Data.Bool using (Bool ; false ; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties
  using (toℕ-injective ; toℕ<n ; toℕ-inject≤) renaming (_≟_ to _≟ᶠ_)
open import Data.Nat using (_<_) renaming (_^_ to _^ℕ_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (zx ; zxℕ ; Σ ; Σ′ ; τ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zxℕ-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (fin ; fin-toℕ ; HFreeʷ ; gen ; nil ; cat ; hf-zx ; gen-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; sgn≡ ; prm≡ ; idSP ; NEG ; SWP ; L ; sp-zx
       ; swapF ; swapF-a ; swapF-b ; swapF-o ; SWP-same ; δ ; δ-here ; δ-≢
       ; SWP-NEG ; SWP-invol ; NEG-invol ; ⊙-assoc ; ⊙-cong ; ⊙-idˡ
       ; hop ; drop ; neg≡ ; ≐-refl ; ≐-sym ; ≐-trans)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Sigma
  using (τ-k ; τ-i ; τ-o ; module Sigma)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- The letters of a `zxℕ`, whether or not they are there

private
  -- Deciding the three indices once.
  lit : ∀ (u : ℕ) (pu : u < N) (x : Fin N) (y : ℕ) (py : y < N) →
        zxℕ {₃₊ m} u (toℕ x) y ≡ zx (fin u pu) x (fin y py)
  lit u pu x y py =
    Eq.trans (Eq.cong₂ (λ s t → zxℕ {₃₊ m} s (toℕ x) t)
                       (Eq.sym (fin-toℕ u pu)) (Eq.sym (fin-toℕ y py)))
             (zxℕ-zx (fin u pu) x (fin y py))

  -- A letter with coinciding X-indices is the empty word.
  zx-same : ∀ (c x : Fin N) → zx {₃₊ m} c x x ≡ ε
  zx-same c x with x ≟ᶠ x
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

-- Its permutation is the transposition, empty or not.
zx-prm : ∀ (c x y v : Fin N) → prm (sp (zx {₃₊ m} c x y)) v ≡ swapF x y v
zx-prm c x y v = go (x ≟ᶠ y)
  where
  go : Dec (x ≡ y) → prm (sp (zx {₃₊ m} c x y)) v ≡ swapF x y v
  go (yes Eq.refl) =
    Eq.trans (Eq.cong (λ w → prm (sp w) v) (zx-same c x))
             (Eq.sym (prm≡ (SWP-same x) v))
  go (no ne) = prm≡ (sp-zx c x y ne) v

-- And it signs nothing but its own index.
zx-sgn : ∀ (c x y v : Fin N) → v ≢ c → sgn (sp (zx {₃₊ m} c x y)) v ≡ false
zx-sgn c x y v nc = go (x ≟ᶠ y)
  where
  go : Dec (x ≡ y) → sgn (sp (zx {₃₊ m} c x y)) v ≡ false
  go (yes Eq.refl) = Eq.cong (λ w → sgn (sp w) v) (zx-same c x)
  go (no ne) =
    Eq.trans (sgn≡ (sp-zx c x y ne) v)
             (Eq.trans (xor-identityʳ (δ c v)) (δ-≢ c v nc))

-- And it carries no Hadamard.
hfree-zx : ∀ (c x y : Fin N) → HFreeʷ (zx {₃₊ m} c x y)
hfree-zx c x y = go (x ≟ᶠ y)
  where
  go : Dec (x ≡ y) → HFreeʷ (zx {₃₊ m} c x y)
  go (yes Eq.refl) = Eq.subst HFreeʷ (Eq.sym (zx-same c x)) nil
  go (no ne)       = Eq.subst HFreeʷ (gen-zx c x y ne) (gen (hf-zx c x y ne))

------------------------------------------------------------------------
-- A transposition of indices is the transposition of their numerals

swapF-τ : ∀ (x y v : Fin N) → toℕ (swapF x y v) ≡ τ (toℕ x) (toℕ y) (toℕ v)
swapF-τ x y v = go (v ≟ᶠ x)
  where
  go : Dec (v ≡ x) → toℕ (swapF x y v) ≡ τ (toℕ x) (toℕ y) (toℕ v)
  go (yes Eq.refl) =
    Eq.trans (Eq.cong toℕ (swapF-a x y)) (Eq.sym (τ-k (toℕ x) (toℕ y)))
  go (no nx) = go′ (v ≟ᶠ y)
    where
    go′ : Dec (v ≡ y) → toℕ (swapF x y v) ≡ τ (toℕ x) (toℕ y) (toℕ v)
    go′ (yes Eq.refl) =
      Eq.trans (Eq.cong toℕ (swapF-b x y)) (Eq.sym (τ-i (toℕ x) (toℕ y)))
    go′ (no ny) =
      Eq.trans (Eq.cong toℕ (swapF-o x y v nx ny))
               (Eq.sym (τ-o (toℕ x) (toℕ y) (toℕ v)
                            (λ e → nx (toℕ-injective e))
                            (λ e → ny (toℕ-injective e))))

------------------------------------------------------------------------
-- Two letters on the same transposition cancel
--
-- `(−1)_[u] X_[x,y] (−1)_[u′] X_[x,y]` is the identity exactly when u
-- is u′ transposed: pushing the second sign left through the first
-- exchange renames it to u, the two signs square away, and so do the
-- two exchanges.  When x and y coincide both letters are the empty
-- word — the same condition on both sides, which is why the pairing is
-- by *transposition* and not by position.

private
  sp≡ : ∀ {u v : W} → u ≡ v → sp u ≗ sp v
  sp≡ Eq.refl = ≐-refl

zx-pair : ∀ (u u′ x y : Fin N) → u ≡ swapF x y u′ →
          sp (zx {₃₊ m} u x y) ⊛ sp (zx {₃₊ m} u′ x y) ≗ idSP
zx-pair u u′ x y e = go (x ≟ᶠ y)
  where
  go : Dec (x ≡ y) → sp (zx {₃₊ m} u x y) ⊛ sp (zx {₃₊ m} u′ x y) ≗ idSP
  go (yes Eq.refl) =
    ≐-trans (⊙-cong (sp≡ (zx-same u x)) (sp≡ (zx-same u′ x))) (⊙-idˡ idSP)
  go (no ne) = ≐-trans (⊙-cong (sp-zx u x y ne) (sp-zx u′ x y ne)) algebra
    where
    algebra : (NEG u ⊛ SWP x y) ⊛ (NEG u′ ⊛ SWP x y) ≗ idSP
    algebra =
      ≐-trans (⊙-assoc (NEG u) (SWP x y) (NEG u′ ⊛ SWP x y))
      (≐-trans (⊙-cong (≐-refl {NEG u})
                 (hop (SWP x y) (NEG u′) (SWP x y) (NEG (swapF x y u′))
                      (SWP x y) (SWP-NEG x y u′)))
      (≐-trans (⊙-cong (≐-refl {NEG u})
                 (⊙-cong (neg≡ (Eq.sym e)) (≐-refl {SWP x y ⊛ SWP x y})))
      (≐-trans (drop (NEG u) (NEG u) (SWP x y ⊛ SWP x y) (NEG-invol u))
               (SWP-invol x y))))

------------------------------------------------------------------------
-- A four-fold telescope

private
  peel : ∀ (f g A B : SP) → (A ⊛ B) ≗ idSP → (f ⊛ A) ⊛ (B ⊛ g) ≗ f ⊛ g
  peel f g A B e =
    ≐-trans (⊙-assoc f A (B ⊛ g))
    (≐-trans (⊙-cong (≐-refl {f}) (≐-sym (⊙-assoc A B g)))
    (≐-trans (⊙-cong (≐-refl {f}) (⊙-cong e (≐-refl {g})))
             (⊙-cong (≐-refl {f}) (⊙-idˡ g))))

  shut : ∀ (f A B g : SP) → (A ⊛ B) ≗ idSP → (f ⊛ g) ≗ idSP →
         (f ⊛ A) ⊛ (B ⊛ g) ≗ idSP
  shut f A B g e e′ = ≐-trans (peel f g A B e) e′

  tele4 : ∀ (f₀ f₁ f₂ f₃ g₃ g₂ g₁ g₀ : SP) →
          (f₃ ⊛ g₃) ≗ idSP → (f₂ ⊛ g₂) ≗ idSP →
          (f₁ ⊛ g₁) ≗ idSP → (f₀ ⊛ g₀) ≗ idSP →
          (f₀ ⊛ (f₁ ⊛ (f₂ ⊛ f₃))) ⊛ (g₃ ⊛ (g₂ ⊛ (g₁ ⊛ g₀))) ≗ idSP
  tele4 f₀ f₁ f₂ f₃ g₃ g₂ g₁ g₀ e₃ e₂ e₁ e₀ =
    ≐-trans (⊙-cong (≐-refl {f₀ ⊛ (f₁ ⊛ (f₂ ⊛ f₃))}) outer)
            (shut f₀ (f₁ ⊛ (f₂ ⊛ f₃)) (g₃ ⊛ (g₂ ⊛ g₁)) g₀ inner e₀)
    where
    outer : g₃ ⊛ (g₂ ⊛ (g₁ ⊛ g₀)) ≗ (g₃ ⊛ (g₂ ⊛ g₁)) ⊛ g₀
    outer = ≐-trans (⊙-cong (≐-refl {g₃}) (≐-sym (⊙-assoc g₂ g₁ g₀)))
                    (≐-sym (⊙-assoc g₃ (g₂ ⊛ g₁) g₀))

    inner : (f₁ ⊛ (f₂ ⊛ f₃)) ⊛ (g₃ ⊛ (g₂ ⊛ g₁)) ≗ idSP
    inner =
      ≐-trans (⊙-cong (≐-refl {f₁ ⊛ (f₂ ⊛ f₃)}) (≐-sym (⊙-assoc g₃ g₂ g₁)))
              (shut f₁ (f₂ ⊛ f₃) (g₃ ⊛ g₂) g₁ (shut f₂ f₃ g₃ g₂ e₃ e₂) e₁)

------------------------------------------------------------------------
-- The numerals 0 … 4 are indices

private
  lit< : ∀ (k : Fin 8) → toℕ k < N
  lit< k = Eq.subst (_< N) (toℕ-inject≤ k _) (toℕ<n (fin8 {m} k))

  b0 b1 b2 b3 b4 : _
  b0 = lit< ₀
  b1 = lit< ₁
  b2 = lit< ₂
  b3 = lit< ₃
  b4 = lit< ₄

------------------------------------------------------------------------
-- Definition E.1's word

module Sig (a b c d : Fin N)
           (ab : a ≢ b) (ac : a ≢ c) (ad : a ≢ d)
           (bc : b ≢ c) (bd : b ≢ d) (cd : c ≢ d)
  where

  private
    ≢ℕ : ∀ {x y : Fin N} → x ≢ y → toℕ x ≢ toℕ y
    ≢ℕ ne e = ne (toℕ-injective e)

  open Sigma (toℕ a) (toℕ b) (toℕ c) (toℕ d)
             (≢ℕ ab) (≢ℕ ac) (≢ℕ ad) (≢ℕ bc) (≢ℕ bd) (≢ℕ cd) public
  open Sigma.Bounds (toℕ a) (toℕ b) (toℕ c) (toℕ d)
                    (≢ℕ ab) (≢ℕ ac) (≢ℕ ad) (≢ℕ bc) (≢ℕ bd) (≢ℕ cd)
                    {N} (toℕ<n a) (toℕ<n b) (toℕ<n c) (toℕ<n d)
                    b0 b1 b2 b3 b4 public

  Σw : W
  Σw = Σ {₃₊ m} (toℕ a) (toℕ b) (toℕ c) (toℕ d)

  private
    -- The four letters, their indices decided.
    A₀ A₁ A₂ A₃ : W
    A₀ = zx (fin m₀ m₀<) a (fin i₀ i₀<)
    A₁ = zx (fin m₁ m₁<) b (fin i₁ i₁<)
    A₂ = zx (fin m₂ m₂<) c (fin i₂ i₂<)
    A₃ = zx (fin m₃ m₃<) d (fin 2 b2)

    Σ≡ : Σw ≡ A₀ • (A₁ • (A₂ • A₃))
    Σ≡ = Eq.cong₂ _•_ (lit m₀ m₀< a i₀ i₀<)
         (Eq.cong₂ _•_ (lit m₁ m₁< b i₁ i₁<)
         (Eq.cong₂ _•_ (lit m₂ m₂< c i₂ i₂<) (lit m₃ m₃< d 2 b2)))

    -- The points the four letters are reached at.
    q₀ q₁ q₂ q₃ : Fin N → Fin N
    q₀ v = v
    q₁ v = swapF a (fin i₀ i₀<) (q₀ v)
    q₂ v = swapF b (fin i₁ i₁<) (q₁ v)
    q₃ v = swapF c (fin i₂ i₂<) (q₂ v)

    -- and their numerals, which are `Sigma`'s.
    q₁-ℕ : ∀ (v : Fin N) → toℕ (q₁ v) ≡ π₀ (toℕ v)
    q₁-ℕ v = Eq.trans (swapF-τ a (fin i₀ i₀<) v)
                      (Eq.cong (λ z → τ (toℕ a) z (toℕ v)) (fin-toℕ i₀ i₀<))

    q₂-ℕ : ∀ (v : Fin N) → toℕ (q₂ v) ≡ π₁ (π₀ (toℕ v))
    q₂-ℕ v =
      Eq.trans (swapF-τ b (fin i₁ i₁<) (q₁ v))
        (Eq.trans (Eq.cong (λ z → τ (toℕ b) z (toℕ (q₁ v))) (fin-toℕ i₁ i₁<))
                  (Eq.cong (τ (toℕ b) i₁) (q₁-ℕ v)))

    q₃-ℕ : ∀ (v : Fin N) → toℕ (q₃ v) ≡ π₂ (π₁ (π₀ (toℕ v)))
    q₃-ℕ v =
      Eq.trans (swapF-τ c (fin i₂ i₂<) (q₂ v))
        (Eq.trans (Eq.cong (λ z → τ (toℕ c) z (toℕ (q₂ v))) (fin-toℕ i₂ i₂<))
                  (Eq.cong (τ (toℕ c) i₂) (q₂-ℕ v)))

  ----------------------------------------------------------------------
  -- Its permutation

  prm-Σ : ∀ (v : Fin N) → toℕ (prm (sp Σw) v) ≡ prmΣ (toℕ v)
  prm-Σ v =
    Eq.trans (Eq.cong (λ w → toℕ (prm (sp w) v)) Σ≡)
    (Eq.trans (Eq.cong toℕ step)
      (Eq.trans (swapF-τ d (fin 2 b2) (q₃ v))
        (Eq.trans (Eq.cong (λ z → τ (toℕ d) z (toℕ (q₃ v))) (fin-toℕ 2 b2))
                  (Eq.cong (τ (toℕ d) 2) (q₃-ℕ v)))))
    where
    step : prm (sp (A₀ • (A₁ • (A₂ • A₃)))) v ≡ swapF d (fin 2 b2) (q₃ v)
    step =
      Eq.trans (zx-prm (fin m₃ m₃<) d (fin 2 b2)
                       (prm (sp A₂) (prm (sp A₁) (prm (sp A₀) v))))
        (Eq.cong (swapF d (fin 2 b2))
          (Eq.trans (Eq.cong (prm (sp A₂))
                      (Eq.trans (Eq.cong (prm (sp A₁))
                                  (zx-prm (fin m₀ m₀<) a (fin i₀ i₀<) v))
                                (zx-prm (fin m₁ m₁<) b (fin i₁ i₁<) (q₁ v))))
                    (zx-prm (fin m₂ m₂<) c (fin i₂ i₂<) (q₂ v))))

  ----------------------------------------------------------------------
  -- Its signs
  --
  -- Each letter signs only its own index, and none of the four points a
  -- letter is reached at on a, b, c or d is one of those.

  private
    sgn-Σ : ∀ (v : Fin N) →
            toℕ v ≢ m₀ → toℕ (q₁ v) ≢ m₁ → toℕ (q₂ v) ≢ m₂ → toℕ (q₃ v) ≢ m₃ →
            sgn (sp Σw) v ≡ false
    sgn-Σ v n₀ n₁ n₂ n₃ =
      Eq.trans (Eq.cong (λ w → sgn (sp w) v) Σ≡)
        (Eq.trans (Eq.cong₂ _xor_ e₀ (Eq.cong₂ _xor_ e₁ (Eq.cong₂ _xor_ e₂ e₃)))
                  Eq.refl)
      where
      ≢fin : ∀ (u : ℕ) (pu : u < N) {x : Fin N} → toℕ x ≢ u → x ≢ fin u pu
      ≢fin u pu nu e = nu (Eq.trans (Eq.cong toℕ e) (fin-toℕ u pu))

      e₀ : sgn (sp A₀) v ≡ false
      e₀ = zx-sgn (fin m₀ m₀<) a (fin i₀ i₀<) v (≢fin m₀ m₀< n₀)

      e₁ : sgn (sp A₁) (prm (sp A₀) v) ≡ false
      e₁ = Eq.trans (Eq.cong (sgn (sp A₁)) (zx-prm (fin m₀ m₀<) a (fin i₀ i₀<) v))
                    (zx-sgn (fin m₁ m₁<) b (fin i₁ i₁<) (q₁ v) (≢fin m₁ m₁< n₁))

      p₁ : prm (sp A₁) (prm (sp A₀) v) ≡ q₂ v
      p₁ = Eq.trans (zx-prm (fin m₁ m₁<) b (fin i₁ i₁<) (prm (sp A₀) v))
                    (Eq.cong (swapF b (fin i₁ i₁<))
                             (zx-prm (fin m₀ m₀<) a (fin i₀ i₀<) v))

      e₂ : sgn (sp A₂) (prm (sp A₁) (prm (sp A₀) v)) ≡ false
      e₂ = Eq.trans (Eq.cong (sgn (sp A₂)) p₁)
                    (zx-sgn (fin m₂ m₂<) c (fin i₂ i₂<) (q₂ v) (≢fin m₂ m₂< n₂))

      p₂ : prm (sp A₂) (prm (sp A₁) (prm (sp A₀) v)) ≡ q₃ v
      p₂ = Eq.trans (zx-prm (fin m₂ m₂<) c (fin i₂ i₂<)
                            (prm (sp A₁) (prm (sp A₀) v)))
                    (Eq.cong (swapF c (fin i₂ i₂<)) p₁)

      e₃ : sgn (sp A₃) (prm (sp A₂) (prm (sp A₁) (prm (sp A₀) v))) ≡ false
      e₃ = Eq.trans (Eq.cong (sgn (sp A₃)) p₂)
                    (zx-sgn (fin m₃ m₃<) d (fin 2 b2) (q₃ v) (≢fin m₃ m₃< n₃))

  sgn-Σ-a : sgn (sp Σw) a ≡ false
  sgn-Σ-a = sgn-Σ a sgn₀-a
                    (Eq.subst (_≢ m₁) (Eq.sym (q₁-ℕ a)) sgn₁-a)
                    (Eq.subst (_≢ m₂) (Eq.sym (q₂-ℕ a)) sgn₂-a)
                    (Eq.subst (_≢ m₃) (Eq.sym (q₃-ℕ a)) sgn₃-a)

  sgn-Σ-b : sgn (sp Σw) b ≡ false
  sgn-Σ-b = sgn-Σ b sgn₀-b
                    (Eq.subst (_≢ m₁) (Eq.sym (q₁-ℕ b)) sgn₁-b)
                    (Eq.subst (_≢ m₂) (Eq.sym (q₂-ℕ b)) sgn₂-b)
                    (Eq.subst (_≢ m₃) (Eq.sym (q₃-ℕ b)) sgn₃-b)

  sgn-Σ-c : sgn (sp Σw) c ≡ false
  sgn-Σ-c = sgn-Σ c sgn₀-c
                    (Eq.subst (_≢ m₁) (Eq.sym (q₁-ℕ c)) sgn₁-c)
                    (Eq.subst (_≢ m₂) (Eq.sym (q₂-ℕ c)) sgn₂-c)
                    (Eq.subst (_≢ m₃) (Eq.sym (q₃-ℕ c)) sgn₃-c)

  sgn-Σ-d : sgn (sp Σw) d ≡ false
  sgn-Σ-d = sgn-Σ d sgn₀-d
                    (Eq.subst (_≢ m₁) (Eq.sym (q₁-ℕ d)) sgn₁-d)
                    (Eq.subst (_≢ m₂) (Eq.sym (q₂-ℕ d)) sgn₂-d)
                    (Eq.subst (_≢ m₃) (Eq.sym (q₃-ℕ d)) sgn₃-d)

  ----------------------------------------------------------------------
  -- Where it sends the four indices

  prm-Σ-a : toℕ (prm (sp Σw) a) ≡ 0
  prm-Σ-a = Eq.trans (prm-Σ a) prmΣ-a

  prm-Σ-b : toℕ (prm (sp Σw) b) ≡ 1
  prm-Σ-b = Eq.trans (prm-Σ b) prmΣ-b

  prm-Σ-c : toℕ (prm (sp Σw) c) ≡ 3
  prm-Σ-c = Eq.trans (prm-Σ c) prmΣ-c

  prm-Σ-d : toℕ (prm (sp Σw) d) ≡ 2
  prm-Σ-d = Eq.trans (prm-Σ d) prmΣ-d

  ----------------------------------------------------------------------
  -- Definition E.1's second word is its inverse
  --
  -- Σ′ has the same four transpositions in the other order, each
  -- carrying the *next* sign up: m₀ = π₀ m₁, m₁ = π₁ m₂, m₂ = π₂ m₃
  -- and m₃ = π₃ 4.  So the letters pair off by transposition and the
  -- product telescopes.

  Σ′w : W
  Σ′w = Σ′ {₃₊ m} (toℕ a) (toℕ b) (toℕ c) (toℕ d)

  private
    B₀ B₁ B₂ B₃ : W
    B₃ = zx (fin 4 b4) d (fin 2 b2)
    B₂ = zx (fin m₃ m₃<) c (fin i₂ i₂<)
    B₁ = zx (fin m₂ m₂<) b (fin i₁ i₁<)
    B₀ = zx (fin m₁ m₁<) a (fin i₀ i₀<)

    Σ′≡ : Σ′w ≡ B₃ • (B₂ • (B₁ • B₀))
    Σ′≡ = Eq.cong₂ _•_ (lit 4 b4 d 2 b2)
          (Eq.cong₂ _•_ (lit m₃ m₃< c i₂ i₂<)
          (Eq.cong₂ _•_ (lit m₂ m₂< b i₁ i₁<) (lit m₁ m₁< a i₀ i₀<)))

    -- Each sign is the next one transposed.
    lift-τ : ∀ (u : ℕ) (pu : u < N) (x : Fin N) (y : ℕ) (py : y < N)
             (w : ℕ) (pw : w < N) → w ≡ τ (toℕ x) y u →
             fin w pw ≡ swapF x (fin y py) (fin u pu)
    lift-τ u pu x y py w pw e =
      toℕ-injective
        (Eq.trans (fin-toℕ w pw)
          (Eq.trans e
            (Eq.sym (Eq.trans (swapF-τ x (fin y py) (fin u pu))
                      (Eq.cong₂ (λ s t → τ (toℕ x) s t)
                                (fin-toℕ y py) (fin-toℕ u pu))))))

    pair₃ : fin m₃ m₃< ≡ swapF d (fin 2 b2) (fin 4 b4)
    pair₃ = lift-τ 4 b4 d 2 b2 m₃ m₃< Eq.refl

    pair₂ : fin m₂ m₂< ≡ swapF c (fin i₂ i₂<) (fin m₃ m₃<)
    pair₂ = lift-τ m₃ m₃< c i₂ i₂< m₂ m₂< Eq.refl

    pair₁ : fin m₁ m₁< ≡ swapF b (fin i₁ i₁<) (fin m₂ m₂<)
    pair₁ = lift-τ m₂ m₂< b i₁ i₁< m₁ m₁< Eq.refl

    pair₀ : fin m₀ m₀< ≡ swapF a (fin i₀ i₀<) (fin m₁ m₁<)
    pair₀ = lift-τ m₁ m₁< a i₀ i₀< m₀ m₀< Eq.refl

  Σ-inv : sp Σw ⊛ sp Σ′w ≗ idSP
  Σ-inv =
    ≐-trans (⊙-cong (sp≡ Σ≡) (sp≡ Σ′≡))
            (tele4 (sp A₀) (sp A₁) (sp A₂) (sp A₃)
                   (sp B₃) (sp B₂) (sp B₁) (sp B₀)
                   (zx-pair (fin m₃ m₃<) (fin 4 b4) d (fin 2 b2) pair₃)
                   (zx-pair (fin m₂ m₂<) (fin m₃ m₃<) c (fin i₂ i₂<) pair₂)
                   (zx-pair (fin m₁ m₁<) (fin m₂ m₂<) b (fin i₁ i₁<) pair₁)
                   (zx-pair (fin m₀ m₀<) (fin m₁ m₁<) a (fin i₀ i₀<) pair₀))

  -- Both are Hadamard-free.
  hfree-Σ : HFreeʷ Σw
  hfree-Σ = Eq.subst HFreeʷ (Eq.sym Σ≡)
    (cat (hfree-zx (fin m₀ m₀<) a (fin i₀ i₀<))
      (cat (hfree-zx (fin m₁ m₁<) b (fin i₁ i₁<))
        (cat (hfree-zx (fin m₂ m₂<) c (fin i₂ i₂<))
             (hfree-zx (fin m₃ m₃<) d (fin 2 b2)))))

  hfree-Σ′ : HFreeʷ Σ′w
  hfree-Σ′ = Eq.subst HFreeʷ (Eq.sym Σ′≡)
    (cat (hfree-zx (fin 4 b4) d (fin 2 b2))
      (cat (hfree-zx (fin m₃ m₃<) c (fin i₂ i₂<))
        (cat (hfree-zx (fin m₂ m₂<) b (fin i₁ i₁<))
             (hfree-zx (fin m₁ m₁<) a (fin i₀ i₀<)))))
