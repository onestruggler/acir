------------------------------------------------------------------------
-- Presentations of groups
--
-- The edge K_[0,1,2,3] at a level with a positive exponent (Lemma
-- A.20, Subcase 3.2).
--
-- Let a < b < c < d be the first four odd entries of the pivot column
-- W / 2ᴷ, and count how many lie among 0..3.
--
-- * One or three: an odd number of odd entries meets K, so every row of
--   2K·W is odd, the exponent rises, and the edge goes up, which is
--   excluded.
-- * None: K meets four even entries, which after K are all odd (the
--   number of odd entries rises: excluded) or all even; then the
--   syllable is unchanged and commutes with K.
-- * Four: the syllable is K (-1)_[0]^t.  If t = 0 it is K itself.  If
--   t = 1, the syllable after K is K (-1)_[0] too (with K alone the
--   path would return to s and drop below it), and
--   K (-1)_[0] K = (-1)_[0] X_[1,2] K (-1)_[0] closes the square.
-- * Two: QuadK2.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadK {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
import Data.Integer.Properties as ℤP
open import Data.List.Base using (List ; [] ; _∷_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal ; Odd ; Even ; half)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ ; one2)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_ ; ColOrth-actMʷ ; actMʷ)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (_<ₗ_ ; <ₗ-irrefl)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl)
open import Examples.Groups.CCX+HH-TwoLevel.Signs {n} using (Mτ-comm)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (gen-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Engine using (prfᶠ ; emb⁼)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; emb ; [_]ᵢ ; _∷ᵢ_)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-lt)
open R {n} using (Path ; act-gg ; _≤ₗ_)
open import Examples.Groups.CCX+HH-TwoLevel.PathTools {n} using (path-cong)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (level-of ; MonoWord)
import Examples.Groups.CCX+HH-TwoLevel.KHalf as KH
import Examples.Groups.CCX+HH-TwoLevel.Rel4 as R4
import Examples.Groups.CCX+HH-TwoLevel.QuadKBase as QKB
import Examples.Groups.CCX+HH-TwoLevel.QuadK2 as QK2

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  ≡⇒≈ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  ≡⇒≈ ≡.refl = refl

  -- Increasing indices in ℕ, read off a bound on the last.
  pos4 : ∀ {i j k l} → i ℕ.< j → j ℕ.< k → k ℕ.< l → l ℕ.≤ 3 → i ≡ 0 × j ≡ 1 × k ≡ 2 × l ≡ 3
  pos4 {i} {j} {k} {l} ij jk kl l3 = i0 , j1 , k2 , l≡
    where
    k≤ : k ℕ.≤ 2
    k≤ = ℕP.≤-pred (ℕP.≤-trans kl l3)
    j≤ : j ℕ.≤ 1
    j≤ = ℕP.≤-pred (ℕP.≤-trans jk k≤)
    i0 : i ≡ 0
    i0 = ℕP.n≤0⇒n≡0 (ℕP.≤-pred (ℕP.≤-trans ij j≤))
    j1 : j ≡ 1
    j1 = ℕP.≤-antisym j≤ (≡.subst (λ x → suc x ℕ.≤ j) i0 ij)
    k2 : k ≡ 2
    k2 = ℕP.≤-antisym k≤ (≡.subst (λ x → suc x ℕ.≤ k) j1 jk)
    l≡ : l ≡ 3
    l≡ = ℕP.≤-antisym l3 (≡.subst (λ x → suc x ℕ.≤ l) k2 kl)

  Pos3 : ℕ → ℕ → ℕ → Set
  Pos3 i j k = (i ≡ 0 × j ≡ 1 × k ≡ 2) ⊎ (i ≡ 0 × j ≡ 1 × k ≡ 3) ⊎ (i ≡ 0 × j ≡ 2 × k ≡ 3) ⊎ (i ≡ 1 × j ≡ 2 × k ≡ 3)

  pos3 : ∀ {i j k} → i ℕ.< j → j ℕ.< k → k ℕ.≤ 3 → Pos3 i j k
  pos3 {i} {j} {k} ij jk k3 = byk (k ℕP.≟ 3)
    where
    low : j ℕ.≤ 1 → i ≡ 0 × j ≡ 1
    low j≤ = i0 , ℕP.≤-antisym j≤ (≡.subst (λ x → suc x ℕ.≤ j) i0 ij)
      where
      i0 = ℕP.n≤0⇒n≡0 (ℕP.≤-pred (ℕP.≤-trans ij j≤))
    byk : Dec (k ≡ 3) → Pos3 i j k
    byk (no k≢3) = inj₁ (proj₁ ij′ , proj₂ ij′ , ℕP.≤-antisym k≤ (≡.subst (λ x → suc x ℕ.≤ k) (proj₂ ij′) jk))
      where
      k≤ : k ℕ.≤ 2
      k≤ = ℕP.≤-pred (ℕP.≤∧≢⇒< k3 k≢3)
      ij′ = low (ℕP.≤-pred (ℕP.≤-trans jk k≤))
    byk (yes k≡3) = byj (j ℕP.≟ 2)
      where
      j≤ : j ℕ.≤ 2
      j≤ = ℕP.≤-pred (≡.subst (λ x → suc j ℕ.≤ x) k≡3 jk)
      byj : Dec (j ≡ 2) → Pos3 i j k
      byj (no j≢2) = inj₂ (inj₁ (proj₁ ij′ , proj₂ ij′ , k≡3))
        where
        ij′ = low (ℕP.≤-pred (ℕP.≤∧≢⇒< j≤ j≢2))
      byj (yes j≡2) = byi (i ℕP.≟ 1)
        where
        i≤ : i ℕ.≤ 1
        i≤ = ℕP.≤-pred (≡.subst (λ x → suc i ℕ.≤ x) j≡2 ij)
        byi : Dec (i ≡ 1) → Pos3 i j k
        byi (yes i≡1) = inj₂ (inj₂ (inj₂ (i≡1 , j≡2 , k≡3)))
        byi (no i≢1) = inj₂ (inj₂ (inj₁ (ℕP.n≤0⇒n≡0 (ℕP.≤-pred (ℕP.≤∧≢⇒< i≤ i≢1)) , j≡2 , k≡3)))

module Edge {P0 P1 P2 P3 : Fin n} .(p01 : P0 < P1) .(p12 : P1 < P2) .(p23 : P2 < P3)
  (z0 : toℕ P0 ≡ 0) (z1 : toℕ P1 ≡ 1) (z2 : toℕ P2 ≡ 2) (z3 : toℕ P3 ≡ 3)
  (le : level (actM (K-gen P0 P1 P2 P3 p01 p12 p23) s) ≤ₗ level s) where

  open QKB s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le

  private
    num≢ : ∀ {x y : Fin n} {i j} → toℕ x ≡ i → toℕ y ≡ j → i ≢ j → x ≢ y
    num≢ ex ey ij e = ij (≡.trans (≡.sym ex) (≡.trans (≡.cong toℕ e) ey))

    -- An index among 0..3 is none beyond.
    lo≢hi : ∀ {x y : Fin n} → toℕ x ℕ.≤ 3 → 3 ℕ.< toℕ y → x ≢ y
    lo≢hi h h′ e = ℕP.<⇒≱ h′ (≡.subst (λ z → toℕ z ℕ.≤ 3) e h)

    P≤3 : ∀ {x : Fin n} {i} → toℕ x ≡ i → i ℕ.≤ 3 → toℕ x ℕ.≤ 3
    P≤3 e h = ≡.subst (ℕ._≤ 3) (≡.sym e) h

    lo<hi : ∀ {x y : Fin n} → toℕ x ℕ.≤ 3 → 3 ℕ.< toℕ y → x < y
    lo<hi h h′ = ℕP.≤-<-trans h h′

    p0 = P≤3 z0 ℕ.z≤n
    p1 = P≤3 z1 (ℕ.s≤s ℕ.z≤n)
    p2 = P≤3 z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
    p3 = P≤3 z3 ℕP.≤-refl

    oa : Odd (W ! a)
    oa = proj₁ (firstOdd-spec W fo)
    ob : Odd (W ! b)
    ob = proj₁ (proj₂ (nextOdd-spec W na))
    oc : Odd (W ! c)
    oc = proj₁ (proj₂ (nextOdd-spec W nb))

    odd-at : ∀ {x y : Fin n} {i} → toℕ x ≡ i → toℕ y ≡ i → Odd (W ! y) → Odd (W ! x)
    odd-at ex ey o = ≡.subst (λ q → Odd (W ! q)) (same ey ex) o

  ------------------------------------------------------------------------
  -- One odd entry among 0..3

  count1 : toℕ a ℕ.≤ 3 → 3 ℕ.< toℕ b → ⊥
  count1 a3 b3 = at (toℕ a) ≡.refl a3
    where
    c3 = ℕP.<-trans b3 b<c
    evl : ∀ {x : Fin n} {i} → toℕ x ≡ i → i ℕ.≤ 3 → x ≢ a → Even (W ! x)
    evl ex i3 xa = ev _ (FinP.<-trans (lo<hi (P≤3 ex i3) c3) c<d) xa (lo≢hi (P≤3 ex i3) b3) (lo≢hi (P≤3 ex i3) c3)
    at : ∀ i → toℕ a ≡ i → i ℕ.≤ 3 → ⊥
    at 0 ea _ = up-par (odd-at z0 ea oa) (evl z1 (ℕ.s≤s ℕ.z≤n) (num≢ z1 ea (λ ())))
                       (evl z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) (num≢ z2 ea (λ ()))) (evl z3 ℕP.≤-refl (num≢ z3 ea (λ ()))) ≡.refl
    at 1 ea _ = up-par (evl z0 ℕ.z≤n (num≢ z0 ea (λ ()))) (odd-at z1 ea oa)
                       (evl z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) (num≢ z2 ea (λ ()))) (evl z3 ℕP.≤-refl (num≢ z3 ea (λ ()))) ≡.refl
    at 2 ea _ = up-par (evl z0 ℕ.z≤n (num≢ z0 ea (λ ()))) (evl z1 (ℕ.s≤s ℕ.z≤n) (num≢ z1 ea (λ ())))
                       (odd-at z2 ea oa) (evl z3 ℕP.≤-refl (num≢ z3 ea (λ ()))) ≡.refl
    at 3 ea _ = up-par (evl z0 ℕ.z≤n (num≢ z0 ea (λ ()))) (evl z1 (ℕ.s≤s ℕ.z≤n) (num≢ z1 ea (λ ())))
                       (evl z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) (num≢ z2 ea (λ ()))) (odd-at z3 ea oa) ≡.refl
    at (suc (suc (suc (suc i)))) _ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))

  ------------------------------------------------------------------------
  -- Three odd entries among 0..3

  count3 : toℕ c ℕ.≤ 3 → 3 ℕ.< toℕ d → ⊥
  count3 c3 d3 = by (pos3 a<b b<c c3)
    where
    evl : ∀ {x : Fin n} {i} → toℕ x ≡ i → i ℕ.≤ 3 → x ≢ a → x ≢ b → x ≢ c → Even (W ! x)
    evl ex i3 xa xb xc = ev _ (lo<hi (P≤3 ex i3) d3) xa xb xc
    by : (toℕ a ≡ 0 × toℕ b ≡ 1 × toℕ c ≡ 2) ⊎ (toℕ a ≡ 0 × toℕ b ≡ 1 × toℕ c ≡ 3) ⊎
         (toℕ a ≡ 0 × toℕ b ≡ 2 × toℕ c ≡ 3) ⊎ (toℕ a ≡ 1 × toℕ b ≡ 2 × toℕ c ≡ 3) → ⊥
    by (inj₁ (ea , eb , ec)) = up-par (odd-at z0 ea oa) (odd-at z1 eb ob) (odd-at z2 ec oc)
      (evl z3 ℕP.≤-refl (num≢ z3 ea (λ ())) (num≢ z3 eb (λ ())) (num≢ z3 ec (λ ()))) ≡.refl
    by (inj₂ (inj₁ (ea , eb , ec))) = up-par (odd-at z0 ea oa) (odd-at z1 eb ob)
      (evl z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) (num≢ z2 ea (λ ())) (num≢ z2 eb (λ ())) (num≢ z2 ec (λ ()))) (odd-at z3 ec oc) ≡.refl
    by (inj₂ (inj₂ (inj₁ (ea , eb , ec)))) = up-par (odd-at z0 ea oa)
      (evl z1 (ℕ.s≤s ℕ.z≤n) (num≢ z1 ea (λ ())) (num≢ z1 eb (λ ())) (num≢ z1 ec (λ ()))) (odd-at z2 eb ob) (odd-at z3 ec oc) ≡.refl
    by (inj₂ (inj₂ (inj₂ (ea , eb , ec)))) =
      up-par (evl z0 ℕ.z≤n (num≢ z0 ea (λ ())) (num≢ z0 eb (λ ())) (num≢ z0 ec (λ ()))) (odd-at z1 ea oa) (odd-at z2 eb ob)
        (odd-at z3 ec oc) ≡.refl

  ------------------------------------------------------------------------
  -- No odd entry among 0..3

  count0 : 3 ℕ.< toℕ a → Path [ gK ]ʷ s o
  count0 a3 = byΣ Σu ≡.refl
    where
    b3 = ℕP.<-trans a3 a<b
    c3 = ℕP.<-trans b3 b<c
    d3 = ℕP.<-trans c3 c<d
    evl : ∀ {x : Fin n} {i} → toℕ x ≡ i → i ℕ.≤ 3 → Even (W ! x)
    evl ex i3 = ev _ (lo<hi (P≤3 ex i3) d3) (lo≢hi (P≤3 ex i3) a3) (lo≢hi (P≤3 ex i3) b3) (lo≢hi (P≤3 ex i3) c3)
    d₀ = half (W ! P0) (evl z0 ℕ.z≤n)
    d₁ = half (W ! P1) (evl z1 (ℕ.s≤s ℕ.z≤n))
    d₂ = half (W ! P2) (evl z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
    d₃ = half (W ! P3) (evl z3 ℕP.≤-refl)
    w0 : W ! P0 ≡ + 0 ℤ.+ + 2 ℤ.* proj₁ d₀
    w0 = ≡.trans (proj₂ d₀) (≡.sym (ℤP.+-identityˡ _))
    w1 : W ! P1 ≡ + 0 ℤ.+ + 2 ℤ.* proj₁ d₁
    w1 = ≡.trans (proj₂ d₁) (≡.sym (ℤP.+-identityˡ _))
    w2 : W ! P2 ≡ + 0 ℤ.+ + 2 ℤ.* proj₁ d₂
    w2 = ≡.trans (proj₂ d₂) (≡.sym (ℤP.+-identityˡ _))
    w3 : W ! P3 ≡ + 0 ℤ.+ + 2 ℤ.* proj₁ d₃
    w3 = ≡.trans (proj₂ d₃) (≡.sym (ℤP.+-identityˡ _))
    open KH.Half W p01 p12 p23 (+ 0) (+ 0) (+ 0) (+ 0) (proj₁ d₀) (proj₁ d₁) (proj₁ d₂) (proj₁ d₃) w0 w1 w2 w3
                 (+ 0) (+ 0) (+ 0) (+ 0) ≡.refl ≡.refl ≡.refl ≡.refl
    hi : ∀ {z : Fin n} → 3 ℕ.< toℕ z → Wh ! z ≡ W ! z
    hi h = Wh-≢ (λ e → lo≢hi p0 h (≡.sym e)) (λ e → lo≢hi p1 h (≡.sym e)) (λ e → lo≢hi p2 h (≡.sym e)) (λ e → lo≢hi p3 h (≡.sym e))
    eq′ : col gs p ≡ scV K′ Wh
    eq′ = ≡.trans colKP (K-col K′)
    mn′ : Minimal K′ Wh
    mn′ = inj₂ (a , ≡.trans (≡.cong oddℤ (hi a3)) oa)
    -- An index is among 0..3 or beyond.
    onP : ∀ z → toℕ z ℕ.≤ 3 → z ≡ P0 ⊎ z ≡ P1 ⊎ z ≡ P2 ⊎ z ≡ P3
    onP z h = at (toℕ z) ≡.refl h
      where
      at : ∀ k → toℕ z ≡ k → k ℕ.≤ 3 → z ≡ P0 ⊎ z ≡ P1 ⊎ z ≡ P2 ⊎ z ≡ P3
      at 0 e _ = inj₁ (same e z0)
      at 1 e _ = inj₂ (inj₁ (same e z1))
      at 2 e _ = inj₂ (inj₂ (inj₁ (same e z2)))
      at 3 e _ = inj₂ (inj₂ (inj₂ (same e z3)))
      at (suc (suc (suc (suc k)))) _ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))
    byΣ : (σ : Bool) → Σu ≡ σ → Path [ gK ]ʷ s o
    -- All four become odd: the number of odd entries rises.
    byΣ true hσ = ⊥-elim (not-up (≡.subst₂ _<ₗ_ (≡.sym lvs) (≡.sym lv′) (inj₂ (≡.refl , inj₂ (≡.refl , more)))))
      where
      lv′ : level gs ≡ (suc (toℕ p) , K′ , nodd Wh)
      lv′ = level-of gs (pivot-g gK P3≤p Wh eq′ mn′) K′ Wh eq′ mn′
      o0 : oddℤ (Wh ! P0) ≡ true
      o0 = ≡.trans (≡.cong oddℤ Wh-a) (≡.trans odd-vA (≡.cong (false xor_) hσ))
      sub : ∀ x → oddℤ (W ! x) ≡ true → oddℤ (Wh ! x) ≡ true
      sub x ox = by (toℕ x ℕP.≤? 3)
        where
        by : Dec (toℕ x ℕ.≤ 3) → oddℤ (Wh ! x) ≡ true
        by (yes h) = ⊥-elim (evodd (onP x h))
          where
          bad : ∀ {y : Fin n} {i} → x ≡ y → toℕ y ≡ i → i ℕ.≤ 3 → ⊥
          bad e ey i3 = case (≡.trans (≡.sym ox) (≡.subst (λ q → Even (W ! q)) (≡.sym e) (evl ey i3)))
            where
            case : true ≡ false → ⊥
            case ()
          evodd : x ≡ P0 ⊎ x ≡ P1 ⊎ x ≡ P2 ⊎ x ≡ P3 → ⊥
          evodd (inj₁ e) = bad e z0 ℕ.z≤n
          evodd (inj₂ (inj₁ e)) = bad e z1 (ℕ.s≤s ℕ.z≤n)
          evodd (inj₂ (inj₂ (inj₁ e))) = bad e z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
          evodd (inj₂ (inj₂ (inj₂ e))) = bad e z3 ℕP.≤-refl
        by (no h) = ≡.trans (≡.cong oddℤ (hi (ℕP.≰⇒> h))) ox
      more : nodd W ℕ.< nodd Wh
      more = count-lt (λ x → oddℤ (Wh ! x)) (λ x → oddℤ (W ! x)) P0 sub o0 (evl z0 ℕ.z≤n)
    -- All four stay even: K commutes with the syllable.
    byΣ false hσ = sandwich gK (sylData p K′ Wh) ε ε pN′ lN′ tt tt rel
      where
      open After Wh eq′ mn′
      par : ∀ x → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
      par x = by (toℕ x ℕP.≤? 3)
        where
        ev′ : ∀ {y : Fin n} {i} → toℕ y ≡ i → i ℕ.≤ 3 → oddℤ (Wh ! y) ≡ false → x ≡ y → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
        ev′ ey i3 h e = ≡.subst (λ q → oddℤ (Wh ! q) ≡ oddℤ (W ! q)) (≡.sym e) (≡.trans h (≡.sym (evl ey i3)))
        by : Dec (toℕ x ℕ.≤ 3) → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
        by (yes h) = at (onP x h)
          where
          at : x ≡ P0 ⊎ x ≡ P1 ⊎ x ≡ P2 ⊎ x ≡ P3 → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
          at (inj₁ e) = ev′ z0 ℕ.z≤n (≡.trans (≡.cong oddℤ Wh-a) (≡.trans odd-vA (≡.cong (false xor_) hσ))) e
          at (inj₂ (inj₁ e)) = ev′ z1 (ℕ.s≤s ℕ.z≤n) (≡.trans (≡.cong oddℤ Wh-b) (≡.trans odd-vB (≡.cong (false xor_) hσ))) e
          at (inj₂ (inj₂ (inj₁ e))) = ev′ z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) (≡.trans (≡.cong oddℤ Wh-c) (≡.trans odd-vC (≡.cong (false xor_) hσ))) e
          at (inj₂ (inj₂ (inj₂ e))) = ev′ z3 ℕP.≤-refl (≡.trans (≡.cong oddℤ Wh-d) (≡.trans odd-vD (≡.cong (false xor_) hσ))) e
        by (no h) = ≡.cong oddℤ (hi (ℕP.≰⇒> h))
      t≡ : σ₄ Wh a b c d ≡ t
      t≡ = ≡.trans (≡.cong₂ (λ u v → ((u xor v) xor τ (Wh ! c)) xor τ (Wh ! d)) (≡.cong τ (hi a3)) (≡.cong τ (hi b3)))
             (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor u) xor v) (≡.cong τ (hi c3)) (≡.cong τ (hi d3)))
      N′≡ : sylData p K′ Wh ≡ syl s
      N′≡ = ≡.trans (syl-same-odd Wh par) (≡.trans (≡.cong (λ q → K a b c d a<b b<c c<d • Mτ a q) t≡) (≡.sym N≡))
      -- K commutes with K_[a,b,c,d] and with (-1)_[a].
      KK : [ gK ]ʷ • K a b c d a<b b<c c<d ≈ K a b c d a<b b<c c<d • [ gK ]ʷ
      KK = axiom (r2f p01 p12 p23 a<b b<c c<d
        (lo≢hi p0 a3) (lo≢hi p0 b3) (lo≢hi p0 c3) (lo≢hi p0 d3) (lo≢hi p1 a3) (lo≢hi p1 b3) (lo≢hi p1 c3) (lo≢hi p1 d3)
        (lo≢hi p2 a3) (lo≢hi p2 b3) (lo≢hi p2 c3) (lo≢hi p2 d3) (lo≢hi p3 a3) (lo≢hi p3 b3) (lo≢hi p3 c3) (lo≢hi p3 d3))
      ap : a ≢ P0 × a ≢ P1 × a ≢ P2 × a ≢ P3
      ap = (λ e → lo≢hi p0 a3 (≡.sym e)) , (λ e → lo≢hi p1 a3 (≡.sym e)) , (λ e → lo≢hi p2 a3 (≡.sym e)) , (λ e → lo≢hi p3 a3 (≡.sym e))
      rel : (ε • ([ gK ]ʷ • ε)) • syl s ≈ sylData p K′ Wh • [ gK ]ʷ
      rel = begin
        (ε • ([ gK ]ʷ • ε)) • syl s                              ≈⟨ cleft trans left-unit right-unit ⟩
        [ gK ]ʷ • syl s                                          ≈⟨ cright ≡⇒≈ N≡ ⟩
        [ gK ]ʷ • (K a b c d a<b b<c c<d • Mτ a t)                ≈⟨ sym assoc ⟩
        ([ gK ]ʷ • K a b c d a<b b<c c<d) • Mτ a t                ≈⟨ cleft KK ⟩
        (K a b c d a<b b<c c<d • [ gK ]ʷ) • Mτ a t                ≈⟨ assoc ⟩
        K a b c d a<b b<c c<d • ([ gK ]ʷ • Mτ a t)                ≈⟨ cright sym (Mτ-comm a t gK ap) ⟩
        K a b c d a<b b<c c<d • (Mτ a t • [ gK ]ʷ)                ≈⟨ sym assoc ⟩
        (K a b c d a<b b<c c<d • Mτ a t) • [ gK ]ʷ                ≈⟨ cleft ≡⇒≈ (≡.sym N≡) ⟩
        syl s • [ gK ]ʷ                                          ≈⟨ cleft ≡⇒≈ (≡.sym N′≡) ⟩
        sylData p K′ Wh • [ gK ]ʷ                                ∎

  ------------------------------------------------------------------------
  -- Four odd entries among 0..3

  count4 : toℕ d ℕ.≤ 3 → Path [ gK ]ʷ s o
  count4 d3 = byt t ≡.refl
    where
    poss = pos4 a<b b<c c<d d3
    a≡ : a ≡ P0
    a≡ = same (proj₁ poss) z0
    b≡ : b ≡ P1
    b≡ = same (proj₁ (proj₂ poss)) z1
    c≡ : c ≡ P2
    c≡ = same (proj₁ (proj₂ (proj₂ poss))) z2
    d≡ : d ≡ P3
    d≡ = same (proj₂ (proj₂ (proj₂ poss))) z3
    K≡gK : K a b c d a<b b<c c<d ≡ [ gK ]ʷ
    K≡gK = K≡ a≡ b≡ c≡ d≡
    N≡′ : ∀ {tv} → t ≡ tv → syl s ≡ [ gK ]ʷ • Mτ P0 tv
    N≡′ ht = ≡.trans N≡ (≡.cong₂ _•_ K≡gK (≡.cong₂ Mτ a≡ ht))
    byt : (tv : Bool) → t ≡ tv → Path [ gK ]ʷ s o
    -- The syllable is K.
    byt false ht = path-cong right-unit s o (≡.subst (λ w → Path w s o) (N≡′ ht) pN)
    -- The syllable is K (-1)_[0].
    byt true ht = byt′ (σ₄ Wh a b c d) ≡.refl
      where
      od : Odd (W ! d)
      od = proj₁ (proj₂ (nextOdd-spec W nc))
      oP0 : Odd (W ! P0)
      oP0 = ≡.subst (λ q → Odd (W ! q)) a≡ oa
      oP1 : Odd (W ! P1)
      oP1 = ≡.subst (λ q → Odd (W ! q)) b≡ ob
      oP2 : Odd (W ! P2)
      oP2 = ≡.subst (λ q → Odd (W ! q)) c≡ oc
      oP3 : Odd (W ! P3)
      oP3 = ≡.subst (λ q → Odd (W ! q)) d≡ od
      d₀ = one2 (W ! P0) oP0
      d₁ = one2 (W ! P1) oP1
      d₂ = one2 (W ! P2) oP2
      d₃ = one2 (W ! P3) oP3
      open KH.Half W p01 p12 p23 (+ 1) (+ 1) (+ 1) (+ 1) (proj₁ d₀) (proj₁ d₁) (proj₁ d₂) (proj₁ d₃)
                   (proj₁ (proj₂ d₀)) (proj₁ (proj₂ d₁)) (proj₁ (proj₂ d₂)) (proj₁ (proj₂ d₃))
                   (+ 2) (+ 0) (+ 0) (+ 0) ≡.refl ≡.refl ≡.refl ≡.refl
      tP : σ₄ W a b c d ≡ σ₄ W P0 P1 P2 P3
      tP = ≡.trans (≡.cong₂ (λ x y → σ₄ W x y c d) a≡ b≡) (≡.cong₂ (λ x y → σ₄ W P0 P1 x y) c≡ d≡)
      -- Σ is t, which is 1.
      Σ≡ : Σu ≡ true
      Σ≡ = ≡.trans (≡.cong₂ (λ u v → ((u xor v) xor oddℤ (proj₁ d₂)) xor oddℤ (proj₁ d₃)) (proj₂ (proj₂ d₀)) (proj₂ (proj₂ d₁)))
             (≡.trans (≡.cong₂ (λ u v → ((τ (W ! P0) xor τ (W ! P1)) xor u) xor v) (proj₂ (proj₂ d₂)) (proj₂ (proj₂ d₃)))
               (≡.trans (≡.sym tP) ht))
      hi : ∀ {z : Fin n} → 3 ℕ.< toℕ z → Wh ! z ≡ W ! z
      hi h = Wh-≢ (λ e → lo≢hi p0 h (≡.sym e)) (λ e → lo≢hi p1 h (≡.sym e)) (λ e → lo≢hi p2 h (≡.sym e)) (λ e → lo≢hi p3 h (≡.sym e))
      -- All four stay odd.
      o0 : oddℤ (Wh ! P0) ≡ true
      o0 = ≡.trans (≡.cong oddℤ Wh-a) (≡.trans odd-vA (≡.cong (false xor_) Σ≡))
      o1 : oddℤ (Wh ! P1) ≡ true
      o1 = ≡.trans (≡.cong oddℤ Wh-b) (≡.trans odd-vB (≡.cong (false xor_) Σ≡))
      o2 : oddℤ (Wh ! P2) ≡ true
      o2 = ≡.trans (≡.cong oddℤ Wh-c) (≡.trans odd-vC (≡.cong (false xor_) Σ≡))
      o3 : oddℤ (Wh ! P3) ≡ true
      o3 = ≡.trans (≡.cong oddℤ Wh-d) (≡.trans odd-vD (≡.cong (false xor_) Σ≡))
      par : ∀ x → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
      par x = by (toℕ x ℕP.≤? 3)
        where
        on : ∀ {y : Fin n} → oddℤ (Wh ! y) ≡ true → Odd (W ! y) → x ≡ y → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
        on h h′ e = ≡.subst (λ q → oddℤ (Wh ! q) ≡ oddℤ (W ! q)) (≡.sym e) (≡.trans h (≡.sym h′))
        at : ∀ k → toℕ x ≡ k → k ℕ.≤ 3 → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
        at 0 e _ = on o0 oP0 (same e z0)
        at 1 e _ = on o1 oP1 (same e z1)
        at 2 e _ = on o2 oP2 (same e z2)
        at 3 e _ = on o3 oP3 (same e z3)
        at (suc (suc (suc (suc k)))) _ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))
        by : Dec (toℕ x ℕ.≤ 3) → oddℤ (Wh ! x) ≡ oddℤ (W ! x)
        by (yes h) = at (toℕ x) ≡.refl h
        by (no h) = ≡.cong oddℤ (hi (ℕP.≰⇒> h))
      eq′ : col gs p ≡ scV K′ Wh
      eq′ = ≡.trans colKP (K-col K′)
      mn′ : Minimal K′ Wh
      mn′ = inj₂ (P0 , o0)
      open After Wh eq′ mn′
      N′≡ : ∀ {tv} → σ₄ Wh a b c d ≡ tv → sylData p K′ Wh ≡ [ gK ]ʷ • Mτ P0 tv
      N′≡ h′ = ≡.trans (syl-same-odd Wh par) (≡.cong₂ _•_ K≡gK (≡.cong₂ Mτ a≡ h′))
      byt′ : (t′ : Bool) → σ₄ Wh a b c d ≡ t′ → Path [ gK ]ʷ s o
      -- With K alone after K the path would return to s, below itself.
      byt′ false h′ = ⊥-elim (<ₗ-irrefl (≡.subst (λ M → level M <ₗ level s) (act-gg gK s)
                        (≡.subst (λ w → level (actMʷ w gs) <ₗ level s) (N′≡ h′) lN′)))
      byt′ true h′ = square gK (sylData p K′ Wh) V pN′ mV rel
        where
        V = M P0 • X P1 P2 p12
        P0≤P3 : P0 ≤ P3
        P0≤P3 = ≡.subst₂ ℕ._≤_ (≡.sym z0) (≡.sym z3) ℕ.z≤n
        P2≤P3 : P2 ≤ P3
        P2≤P3 = ≡.subst₂ ℕ._≤_ (≡.sym z2) (≡.sym z3) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
        mV : MonoWord p V
        mV = ℕP.≤-trans P0≤P3 P3≤p , ℕP.≤-trans P2≤P3 P3≤p
        rc : ∀ {u v : Fin n} → .(u < v) → u < v
        rc {u} {v} lt = recompute (u FinP.<? v) lt
        e4 : Emb 4 n
        e4 = emb (P0 ∷ᵛ P1 ∷ᵛ P2 ∷ᵛ P3 ∷ᵛ []ᵛ) (rc p01 ∷ᵢ rc p12 ∷ᵢ rc p23 ∷ᵢ [ P3 ]ᵢ)
        Kw = [ gK ]ʷ
        M0 = M P0
        -- K (-1)_[0] K (-1)_[0] K = (-1)_[0] X_[1,2].
        kk : Kw • (M0 • (Kw • (M0 • Kw))) ≈ M0 • X P1 P2 p12
        kk = prfᶠ (emb⁼ e4 R4.kmkmk)
        KKM : Kw • (Kw • M0) ≈ M0
        KKM = trans (sym assoc) (trans (cleft gen-gen gK) left-unit)
        kmk : V • (Kw • M0) ≈ (Kw • M0) • Kw
        kmk = begin
          (M0 • X P1 P2 p12) • (Kw • M0)                    ≈⟨ cleft sym kk ⟩
          (Kw • (M0 • (Kw • (M0 • Kw)))) • (Kw • M0)        ≈⟨ assoc ⟩
          Kw • ((M0 • (Kw • (M0 • Kw))) • (Kw • M0))        ≈⟨ cright assoc ⟩
          Kw • (M0 • ((Kw • (M0 • Kw)) • (Kw • M0)))        ≈⟨ cright cright assoc ⟩
          Kw • (M0 • (Kw • ((M0 • Kw) • (Kw • M0))))        ≈⟨ cright cright cright assoc ⟩
          Kw • (M0 • (Kw • (M0 • (Kw • (Kw • M0)))))        ≈⟨ cright cright cright cright KKM ⟩
          Kw • (M0 • (Kw • (M0 • M0)))                      ≈⟨ cright cright cright gen-gen (M-gen P0) ⟩
          Kw • (M0 • (Kw • ε))                              ≈⟨ cright cright right-unit ⟩
          Kw • (M0 • Kw)                                    ≈⟨ sym assoc ⟩
          (Kw • M0) • Kw                                    ∎
        rel : V • syl s ≈ sylData p K′ Wh • Kw
        rel = begin
          V • syl s                ≈⟨ cright ≡⇒≈ (N≡′ ht) ⟩
          V • (Kw • M0)            ≈⟨ kmk ⟩
          (Kw • M0) • Kw           ≈⟨ cleft ≡⇒≈ (≡.sym (N′≡ h′)) ⟩
          sylData p K′ Wh • Kw     ∎

  ------------------------------------------------------------------------
  -- The edge

  edge : Path [ gK ]ʷ s o
  edge = byd (toℕ d ℕP.≤? 3)
    where
    bya : Dec (toℕ a ℕ.≤ 3) → 3 ℕ.< toℕ b → Path [ gK ]ʷ s o
    bya (yes a3) b3 = ⊥-elim (count1 a3 b3)
    bya (no a3) _ = count0 (ℕP.≰⇒> a3)
    byb : Dec (toℕ b ℕ.≤ 3) → 3 ℕ.< toℕ c → Path [ gK ]ʷ s o
    byb (yes b3) c3 = QK2.edge-K2 s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le b3 c3
    byb (no b3) _ = bya (toℕ a ℕP.≤? 3) (ℕP.≰⇒> b3)
    byc : Dec (toℕ c ℕ.≤ 3) → 3 ℕ.< toℕ d → Path [ gK ]ʷ s o
    byc (yes c3) d3 = ⊥-elim (count3 c3 d3)
    byc (no c3) _ = byb (toℕ b ℕP.≤? 3) (ℕP.≰⇒> c3)
    byd : Dec (toℕ d ℕ.≤ 3) → Path [ gK ]ʷ s o
    byd (yes d3) = count4 d3
    byd (no d3) = byc (toℕ c ℕP.≤? 3) (ℕP.≰⇒> d3)

------------------------------------------------------------------------
-- The edge K_[0,1,2,3] out of s, when it does not go up

edge-K : (P0 P1 P2 P3 : Fin n) .(p01 : P0 < P1) .(p12 : P1 < P2) .(p23 : P2 < P3) →
         toℕ P0 ≡ 0 → toℕ P1 ≡ 1 → toℕ P2 ≡ 2 → toℕ P3 ≡ 3 →
         level (actM (K-gen P0 P1 P2 P3 p01 p12 p23) s) ≤ₗ level s → Path (K P0 P1 P2 P3 p01 p12 p23) s o
edge-K P0 P1 P2 P3 p01 p12 p23 z0 z1 z2 z3 le = Edge.edge p01 p12 p23 z0 z1 z2 z3 le
