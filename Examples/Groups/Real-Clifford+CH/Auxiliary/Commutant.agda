------------------------------------------------------------------------
-- Presentations of groups
--
-- What commutes with a Hadamard pair
--
-- Lemma A.6's content: a signed permutation commuting with
-- H_[p,q] H_[r,s] must send p and r to p or r, and q and s to q or s.
-- That is what says a Hadamard-free word commuting with a Hadamard
-- pair is, up to signs, either the identity or the double exchange
-- (X_[p,r] X_[q,s]) on those four indices and anything at all
-- elsewhere — the form A.6 gives it, and the gateway to Equation (65)
-- and so to the whole of Figure 10.
--
-- The argument is the diagonal.  A signed permutation has one entry
-- per row, so the product one way round is just the pair's row at the
-- image; the other way round the pair's own row is a combination of
-- two deltas, and only one of them survives at the image.  Comparing
-- them at the image gives the pair's diagonal entry there, and ±1
-- cancels; the pair's diagonal is +√2 on the first index of each of
-- its pairs, −√2 on the second and 2 elsewhere, three different
-- elements of ℤ[√2], so that entry says where the index went.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Commutant (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.HadamardPair m

private
  n : ℕ
  n = ₃₊ m

module Pair (p q r s : Bits n)
            (pq : p ≢ q) (rs : r ≢ s)
            (pr : p ≢ r) (ps : p ≢ s) (qr : q ≢ r) (qs : q ≢ s)
            (sg : Bits n → Bool) (pm : Bits n → Bits n)
            (pm-inj : ∀ {x y : Bits n} → pm x ≡ pm y → x ≡ y)
  where

  open Entries p q r s pq rs pr ps qr qs
  open Diagonal p q r s pq rs pr ps qr qs

  σ : Bits n → 𝔽
  σ x = if sg x then -1# else 1#

  -- The signed permutation as a matrix, and the pair.
  P : Op n
  P x y = σ x * δb (pm x) y

  M : Op n
  M = HH2 p q r s

  ------------------------------------------------------------------------
  -- The two products, row by row

  -- One row of P is one delta, so the pair's row at the image is all
  -- that survives.
  left : ∀ (x y : Bits n) → (P ⊙ M) x y ≡ σ x * M (pm x) y
  left x y = row-one (σ x) (pm x) P M x (λ _ → Eq.refl) y

  -- The pair's own rows, in the shape `row-two` wants.
  private
    M-p : ∀ (y : Bits n) → M p y ≡ √2 * δb p y + √2 * δb q y
    M-p = HH2-p

    M-q : ∀ (y : Bits n) → M q y ≡ √2 * δb p y + (-1# * √2) * δb q y
    M-q y = Eq.trans (HH2-q y)
                     (Eq.cong (√2 * δb p y +_) (Eq.sym (*-assoc -1# √2 (δb q y))))

    M-r : ∀ (y : Bits n) → M r y ≡ √2 * δb r y + √2 * δb s y
    M-r y = Eq.trans (HH2-r y)
              (Eq.trans (Eq.cong (√2 *_) (Eq.cong₂ _+_ (*-identityˡ (δb r y))
                                                       (*-identityˡ (δb s y))))
                        (*-distribˡ-+ √2 (δb r y) (δb s y)))

    M-s : ∀ (y : Bits n) → M s y ≡ √2 * δb r y + (-1# * √2) * δb s y
    M-s y = Eq.trans (HH2-s y)
              (Eq.trans (Eq.cong (√2 *_) (Eq.cong (_+ -1# * δb s y)
                                                  (*-identityˡ (δb r y))))
                (Eq.trans (*-distribˡ-+ √2 (δb r y) (-1# * δb s y))
                          (Eq.cong (√2 * δb r y +_)
                            (Eq.trans (Eq.sym (*-assoc √2 -1# (δb s y)))
                                      (Eq.cong (_* δb s y) (*-comm √2 -1#))))))

  right : ∀ (c d : 𝔽) (i j x : Bits n) → (∀ y → M x y ≡ c * δb i y + d * δb j y) →
          ∀ (y : Bits n) → (M ⊙ P) x y ≡ c * P i y + d * P j y
  right c d i j x e y = row-two c d i j M P x e y

  ------------------------------------------------------------------------
  -- One entry of the image, picked out

  private
    -- At its own image a row of P is its sign, and at any other row's
    -- image it is zero.
    P-hit : ∀ (x : Bits n) → P x (pm x) ≡ σ x
    P-hit x = Eq.trans (Eq.cong (σ x *_) (δb-refl (pm x))) (*-identityʳ (σ x))

    P-miss : ∀ (x z : Bits n) → x ≢ z → P x (pm z) ≡ 0#
    P-miss x z ne = Eq.trans (Eq.cong (σ x *_) (δ≢ (pm x) (pm z) (λ e → ne (pm-inj e))))
                             (*-zeroʳ (σ x))

    -- So comparing the two products at the image of x leaves the
    -- pair's diagonal entry there, times the sign.
    pick : ∀ (c d : 𝔽) (i j x : Bits n) → (∀ y → M x y ≡ c * δb i y + d * δb j y) →
           i ≡ x → j ≢ x →
           ((P ⊙ M) ≐ (M ⊙ P)) → σ x * M (pm x) (pm x) ≡ σ x * c
    pick c d i j x e i≡x j≢x comm =
      Eq.trans (Eq.sym (left x (pm x)))
        (Eq.trans (comm x (pm x))
          (Eq.trans (right c d i j x e (pm x))
            (Eq.trans (Eq.cong₂ _+_
                        (Eq.cong (c *_) (Eq.trans (Eq.cong (λ z → P z (pm x)) i≡x)
                                                  (P-hit x)))
                        (Eq.cong (d *_) (P-miss j x (λ z → j≢x z))))
              (Eq.trans (Eq.cong (c * σ x +_) (*-zeroʳ d))
                (Eq.trans (+-identityʳ (c * σ x)) (*-comm c (σ x)))))))

  ------------------------------------------------------------------------
  -- Lemma A.6, the part that pins the permutation

  module Commuting (comm : (P ⊙ M) ≐ (M ⊙ P)) where

    -- Each of the four indices goes to one of the two that carry the
    -- same diagonal entry.
    image-p : pm p ≡ p ⊎ pm p ≡ r
    image-p = diag-is-√2 (pm p)
                (sign-cancel (sg p) (M (pm p) (pm p)) √2
                             (pick √2 √2 p q p M-p Eq.refl (λ e → pq (Eq.sym e)) comm))

    image-r : pm r ≡ p ⊎ pm r ≡ r
    image-r = diag-is-√2 (pm r)
                (sign-cancel (sg r) (M (pm r) (pm r)) √2
                             (pick √2 √2 r s r M-r Eq.refl (λ e → rs (Eq.sym e)) comm))

    image-q : pm q ≡ q ⊎ pm q ≡ s
    image-q = diag-is--√2 (pm q)
                (sign-cancel (sg q) (M (pm q) (pm q)) (-1# * √2)
                             (pick′ √2 (-1# * √2) p q q M-q (λ e → pq e) Eq.refl comm))
      where
      -- the surviving delta is the *second* one here
      pick′ : ∀ (c d : 𝔽) (i j x : Bits n) →
              (∀ y → M x y ≡ c * δb i y + d * δb j y) → i ≢ x → j ≡ x →
              ((P ⊙ M) ≐ (M ⊙ P)) → σ x * M (pm x) (pm x) ≡ σ x * d
      pick′ c d i j x e i≢x j≡x cm =
        Eq.trans (Eq.sym (left x (pm x)))
          (Eq.trans (cm x (pm x))
            (Eq.trans (right c d i j x e (pm x))
              (Eq.trans (Eq.cong₂ _+_ (Eq.cong (c *_) (P-miss i x i≢x))
                                      (Eq.cong (d *_)
                                        (Eq.trans (Eq.cong (λ z → P z (pm x)) j≡x)
                                                  (P-hit x))))
                (Eq.trans (Eq.cong (_+ d * σ x) (*-zeroʳ c))
                  (Eq.trans (+-identityˡ (d * σ x)) (*-comm d (σ x)))))))

    image-s : pm s ≡ q ⊎ pm s ≡ s
    image-s = diag-is--√2 (pm s)
                (sign-cancel (sg s) (M (pm s) (pm s)) (-1# * √2)
                             (pick′ √2 (-1# * √2) r s s M-s (λ e → rs e) Eq.refl comm))
      where
      pick′ : ∀ (c d : 𝔽) (i j x : Bits n) →
              (∀ y → M x y ≡ c * δb i y + d * δb j y) → i ≢ x → j ≡ x →
              ((P ⊙ M) ≐ (M ⊙ P)) → σ x * M (pm x) (pm x) ≡ σ x * d
      pick′ c d i j x e i≢x j≡x cm =
        Eq.trans (Eq.sym (left x (pm x)))
          (Eq.trans (cm x (pm x))
            (Eq.trans (right c d i j x e (pm x))
              (Eq.trans (Eq.cong₂ _+_ (Eq.cong (c *_) (P-miss i x i≢x))
                                      (Eq.cong (d *_)
                                        (Eq.trans (Eq.cong (λ z → P z (pm x)) j≡x)
                                                  (P-hit x))))
                (Eq.trans (Eq.cong (_+ d * σ x) (*-zeroʳ c))
                  (Eq.trans (+-identityˡ (d * σ x)) (*-comm d (σ x)))))))

    -- And an index away from both pairs stays away from them: there
    -- the pair is twice the identity, so its row is a single delta and
    -- the same comparison applies.
    image-o : ∀ (x : Bits n) → Outside x → Outside (pm x)
    image-o x (xp , xq , xr , xs) =
      diag-is-2 (pm x)
        (sign-cancel (sg x) (M (pm x) (pm x)) (√2 * √2)
          (Eq.trans (Eq.sym (left x (pm x)))
            (Eq.trans (comm x (pm x))
              (Eq.trans (row-one (√2 * √2) x M P x M-o (pm x))
                (Eq.trans (Eq.cong ((√2 * √2) *_) (P-hit x))
                          (*-comm (√2 * √2) (σ x)))))))
      where
      M-o : ∀ (y : Bits n) → M x y ≡ (√2 * √2) * δb x y
      M-o y = Eq.trans (HH2-o x xp xq xr xs y) (Eq.sym (*-assoc √2 √2 (δb x y)))

    -- Injectivity leaves only two possibilities on each pair: it is
    -- fixed pointwise, or it is exchanged.
    images-pr : (pm p ≡ p × pm r ≡ r) ⊎ (pm p ≡ r × pm r ≡ p)
    images-pr = go image-p image-r
      where
      go : pm p ≡ p ⊎ pm p ≡ r → pm r ≡ p ⊎ pm r ≡ r →
           (pm p ≡ p × pm r ≡ r) ⊎ (pm p ≡ r × pm r ≡ p)
      go (inj₁ ep) (inj₁ er) = ⊥-elim (pr (pm-inj (Eq.trans ep (Eq.sym er))))
      go (inj₁ ep) (inj₂ er) = inj₁ (ep , er)
      go (inj₂ ep) (inj₁ er) = inj₂ (ep , er)
      go (inj₂ ep) (inj₂ er) = ⊥-elim (pr (pm-inj (Eq.trans ep (Eq.sym er))))

    images-qs : (pm q ≡ q × pm s ≡ s) ⊎ (pm q ≡ s × pm s ≡ q)
    images-qs = go image-q image-s
      where
      go : pm q ≡ q ⊎ pm q ≡ s → pm s ≡ q ⊎ pm s ≡ s →
           (pm q ≡ q × pm s ≡ s) ⊎ (pm q ≡ s × pm s ≡ q)
      go (inj₁ eq) (inj₁ es) = ⊥-elim (qs (pm-inj (Eq.trans eq (Eq.sym es))))
      go (inj₁ eq) (inj₂ es) = inj₁ (eq , es)
      go (inj₂ eq) (inj₁ es) = inj₂ (eq , es)
      go (inj₂ eq) (inj₂ es) = ⊥-elim (qs (pm-inj (Eq.trans eq (Eq.sym es))))

    ------------------------------------------------------------------
    -- The two pairs move together, and the signs pair up
    --
    -- The diagonal placed each index; an *off*-diagonal entry says the
    -- two pairs cannot move independently, since the pair's entry at
    -- (p , s) — one index from each of its pairs — is zero while the
    -- comparison there is √2 times a sign, which is not.

    private
      M-pq : M p q ≡ √2
      M-pq = Eq.trans (HH2-p q)
               (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (√2 *_) (δ≢ p q pq))
                                                 (*-zeroʳ √2))
                                       (Eq.trans (Eq.cong (√2 *_) (δb-refl q))
                                                 (*-identityʳ √2)))
                         (+-identityˡ √2))

      M-ps : M p s ≡ 0#
      M-ps = Eq.trans (HH2-p s)
               (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (√2 *_) (δ≢ p s ps))
                                                 (*-zeroʳ √2))
                                       (Eq.trans (Eq.cong (√2 *_) (δ≢ q s qs))
                                                 (*-zeroʳ √2)))
                         (+-identityʳ 0#))

      M-rs : M r s ≡ √2
      M-rs = Eq.trans (HH2-r s)
               (Eq.trans (Eq.cong (√2 *_)
                           (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (1# *_) (δ≢ r s rs))
                                                             (*-zeroʳ 1#))
                                                   (Eq.trans (Eq.cong (1# *_) (δb-refl s))
                                                             (*-identityʳ 1#)))
                                     (+-identityˡ 1#)))
                         (*-identityʳ √2))

      M-rq : M r q ≡ 0#
      M-rq = Eq.trans (HH2-r q)
               (Eq.trans (Eq.cong (√2 *_)
                           (Eq.trans (Eq.cong₂ _+_
                                       (Eq.trans (Eq.cong (1# *_)
                                                   (δ≢ r q (λ e → qr (Eq.sym e))))
                                                 (*-zeroʳ 1#))
                                       (Eq.trans (Eq.cong (1# *_)
                                                   (δ≢ s q (λ e → qs (Eq.sym e))))
                                                 (*-zeroʳ 1#)))
                                     (+-identityʳ 0#)))
                         (*-zeroʳ √2))

      -- The comparison one column across.
      off : ∀ (c d : 𝔽) (i j x z : Bits n) →
            (∀ y → M x y ≡ c * δb i y + d * δb j y) → i ≢ z → j ≡ z →
            σ x * M (pm x) (pm z) ≡ d * σ z
      off c d i j x z e i≢z j≡z =
        Eq.trans (Eq.sym (left x (pm z)))
          (Eq.trans (comm x (pm z))
            (Eq.trans (right c d i j x e (pm z))
              (Eq.trans (Eq.cong₂ _+_
                          (Eq.trans (Eq.cong (c *_) (P-miss i z i≢z)) (*-zeroʳ c))
                          (Eq.cong (d *_) (Eq.trans (Eq.cong (λ w → P w (pm z)) j≡z)
                                                    (P-hit z))))
                        (+-identityˡ (d * σ z)))))

    -- If p stays put then so does q, and if p moves to r then q moves
    -- to s: the exchange is of both pairs or neither.
    together : pm p ≡ p → pm q ≡ q
    together ep = go images-qs
      where
      go : (pm q ≡ q × pm s ≡ s) ⊎ (pm q ≡ s × pm s ≡ q) → pm q ≡ q
      go (inj₁ (eq , _)) = eq
      go (inj₂ (eq , _)) =
        ⊥-elim (√2·≢0 (sg q)
          (Eq.trans (Eq.sym (off √2 √2 p q p q M-p (λ e → pq e) Eq.refl)) zero))
        where
        zero : σ p * M (pm p) (pm q) ≡ 0#
        zero = Eq.trans (Eq.cong (λ w → σ p * M w (pm q)) ep)
                 (Eq.trans (Eq.cong (λ w → σ p * M p w) eq)
                           (Eq.trans (Eq.cong (σ p *_) M-ps) (*-zeroʳ (σ p))))

    together′ : pm p ≡ r → pm q ≡ s
    together′ ep = go images-qs
      where
      go : (pm q ≡ q × pm s ≡ s) ⊎ (pm q ≡ s × pm s ≡ q) → pm q ≡ s
      go (inj₂ (eq , _)) = eq
      go (inj₁ (eq , _)) =
        ⊥-elim (√2·≢0 (sg q)
          (Eq.trans (Eq.sym (off √2 √2 p q p q M-p (λ e → pq e) Eq.refl)) zero))
        where
        zero : σ p * M (pm p) (pm q) ≡ 0#
        zero = Eq.trans (Eq.cong (λ w → σ p * M w (pm q)) ep)
                 (Eq.trans (Eq.cong (λ w → σ p * M r w) eq)
                           (Eq.trans (Eq.cong (σ p *_) M-rq) (*-zeroʳ (σ p))))

    -- And the two signs of each of the pair's own pairs agree.
    sign-pq : pm p ≡ p → sg p ≡ sg q
    sign-pq ep = sign-from (sg p) (sg q)
      (Eq.trans (Eq.sym entry) (off √2 √2 p q p q M-p (λ e → pq e) Eq.refl))
      where
      entry : σ p * M (pm p) (pm q) ≡ σ p * √2
      entry = Eq.trans (Eq.cong (λ w → σ p * M w (pm q)) ep)
                (Eq.trans (Eq.cong (λ w → σ p * M p w) (together ep))
                          (Eq.cong (σ p *_) M-pq))

    sign-rs : pm r ≡ r → pm s ≡ s → sg r ≡ sg s
    sign-rs er es = sign-from (sg r) (sg s)
      (Eq.trans (Eq.sym entry) (off √2 √2 r s r s M-r (λ e → rs e) Eq.refl))
      where
      entry : σ r * M (pm r) (pm s) ≡ σ r * √2
      entry = Eq.trans (Eq.cong (λ w → σ r * M w (pm s)) er)
                (Eq.trans (Eq.cong (λ w → σ r * M r w) es) (Eq.cong (σ r *_) M-rs))

    -- The same, on the exchanged branch: the entry read off is then
    -- the pair's at (r , s) rather than at (p , q), which is the same.
    sign-pq′ : pm p ≡ r → sg p ≡ sg q
    sign-pq′ ep = sign-from (sg p) (sg q)
      (Eq.trans (Eq.sym entry) (off √2 √2 p q p q M-p (λ e → pq e) Eq.refl))
      where
      entry : σ p * M (pm p) (pm q) ≡ σ p * √2
      entry = Eq.trans (Eq.cong (λ w → σ p * M w (pm q)) ep)
                (Eq.trans (Eq.cong (λ w → σ p * M r w) (together′ ep))
                          (Eq.cong (σ p *_) M-rs))

    sign-rs′ : pm r ≡ p → pm s ≡ q → sg r ≡ sg s
    sign-rs′ er es = sign-from (sg r) (sg s)
      (Eq.trans (Eq.sym entry) (off √2 √2 r s r s M-r (λ e → rs e) Eq.refl))
      where
      entry : σ r * M (pm r) (pm s) ≡ σ r * √2
      entry = Eq.trans (Eq.cong (λ w → σ r * M w (pm s)) er)
                (Eq.trans (Eq.cong (λ w → σ r * M p w) es) (Eq.cong (σ r *_) M-pq))

    ------------------------------------------------------------------------
    -- Lemma A.6's conclusion, packaged
    --
    -- The four indices are fixed together or exchanged together, and
    -- along each of the pair's own pairs the two signs agree.  Nothing
    -- else about the permutation matters: `image-o` says it keeps the
    -- rest of the indices among themselves, and every word over them
    -- crosses the pair by (38).

    private
      s-fix : pm q ≡ q → pm s ≡ s
      s-fix eq = go images-qs
        where
        go : (pm q ≡ q × pm s ≡ s) ⊎ (pm q ≡ s × pm s ≡ q) → pm s ≡ s
        go (inj₁ (_ , es))  = es
        go (inj₂ (eq′ , _)) = ⊥-elim (qs (Eq.trans (Eq.sym eq) eq′))

      s-exc : pm q ≡ s → pm s ≡ q
      s-exc eq = go images-qs
        where
        go : (pm q ≡ q × pm s ≡ s) ⊎ (pm q ≡ s × pm s ≡ q) → pm s ≡ q
        go (inj₂ (_ , es))  = es
        go (inj₁ (eq′ , _)) = ⊥-elim (qs (Eq.sym (Eq.trans (Eq.sym eq) eq′)))

    places : (pm p ≡ p × pm q ≡ q × pm r ≡ r × pm s ≡ s)
           ⊎ (pm p ≡ r × pm q ≡ s × pm r ≡ p × pm s ≡ q)
    places = go images-pr
      where
      go : (pm p ≡ p × pm r ≡ r) ⊎ (pm p ≡ r × pm r ≡ p) →
           (pm p ≡ p × pm q ≡ q × pm r ≡ r × pm s ≡ s)
           ⊎ (pm p ≡ r × pm q ≡ s × pm r ≡ p × pm s ≡ q)
      go (inj₁ (ep , er)) = inj₁ (ep , together ep , er , s-fix (together ep))
      go (inj₂ (ep , er)) = inj₂ (ep , together′ ep , er , s-exc (together′ ep))

    signs : (sg p ≡ sg q) × (sg r ≡ sg s)
    signs = go places
      where
      go : (pm p ≡ p × pm q ≡ q × pm r ≡ r × pm s ≡ s)
           ⊎ (pm p ≡ r × pm q ≡ s × pm r ≡ p × pm s ≡ q) →
           (sg p ≡ sg q) × (sg r ≡ sg s)
      go (inj₁ (ep , _ , er , es)) = sign-pq ep , sign-rs er es
      go (inj₂ (ep , _ , er , es)) = sign-pq′ ep , sign-rs′ er es
