------------------------------------------------------------------------
-- Presentations of groups
--
-- Tools for the edge K_[0,1,2,3] at a positive exponent when exactly
-- two of the first four odd entries, a and b, lie among 0..3.
--
-- After K the column agrees in parity with W beyond 3, so if its odd
-- entries among 0..3 are x < y, its first four odd entries are x, y,
-- c, d (chain).  The relations of Rel6 hold on the indices 0, 1, 2, 3,
-- c, d (eQ), where their words of X's and (-1)'s stay below p
-- (mono-emb) and they give the square of QuadBase.sandwich (cfg-rel).
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
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadK2Base {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s))
  {P0 P1 P2 P3 : Fin n} .(p01 : P0 < P1) .(p12 : P1 < P2) .(p23 : P2 < P3)
  (z0 : toℕ P0 ≡ 0) (z1 : toℕ P1 ≡ 1) (z2 : toℕ P2 ≡ 2) (z3 : toℕ P3 ≡ 3)
  (le : R._≤ₗ_ {n} (level (actM (K-gen P0 P1 P2 P3 p01 p12 p23) s)) (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_ ; _∧_ ; if_then_else_)
import Data.Fin.Base as F
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties using (map-++)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec ; lookup) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ ; oddℤ-+ ; oddℤ-*)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (Odd ; Even)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_)
open import Examples.Groups.CCX+HH-TwoLevel.Engine using (Eqn ; lhs ; rhs ; prf ; emb⁼ ; ⟪_⟫ ; ⟪++⟫)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; emb ; gen ; [_]ᵢ ; _∷ᵢ_)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (MonoWord)

open import Examples.Groups.CCX+HH-TwoLevel.QuadKBase s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le public

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

module Count2 (b3 : toℕ b ℕ.≤ 3) (c3 : 3 ℕ.< toℕ c) where

  ------------------------------------------------------------------------
  -- Indices

  -- An index among 0..3 is one of P0..P3.
  onP : ∀ z → toℕ z ℕ.≤ 3 → z ≡ P0 ⊎ z ≡ P1 ⊎ z ≡ P2 ⊎ z ≡ P3
  onP z h = at (toℕ z) ≡.refl h
    where
    at : ∀ k → toℕ z ≡ k → k ℕ.≤ 3 → z ≡ P0 ⊎ z ≡ P1 ⊎ z ≡ P2 ⊎ z ≡ P3
    at 0 e _ = inj₁ (same e z0)
    at 1 e _ = inj₂ (inj₁ (same e z1))
    at 2 e _ = inj₂ (inj₂ (inj₁ (same e z2)))
    at 3 e _ = inj₂ (inj₂ (inj₂ (same e z3)))
    at (suc (suc (suc (suc k)))) _ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))

  -- Indices among 0..3 lie before c and d.
  low<c : ∀ {z : Fin n} → toℕ z ℕ.≤ 3 → z < c
  low<c h = ℕP.≤-<-trans h c3

  low<d : ∀ {z : Fin n} → toℕ z ℕ.≤ 3 → z < d
  low<d h = FinP.<-trans (low<c h) c<d

  low≢c : ∀ {z : Fin n} → toℕ z ℕ.≤ 3 → z ≢ c
  low≢c h e = ℕP.<-irrefl (≡.cong toℕ e) (low<c h)

  low≢d : ∀ {z : Fin n} → toℕ z ℕ.≤ 3 → z ≢ d
  low≢d h e = ℕP.<-irrefl (≡.cong toℕ e) (low<d h)

  ≤3 : ∀ {z : Fin n} {i} → toℕ z ≡ i → i ℕ.≤ 3 → toℕ z ℕ.≤ 3
  ≤3 e h = ≡.subst (ℕ._≤ 3) (≡.sym e) h

  ------------------------------------------------------------------------
  -- The first four odd entries after K

  module Chain (W′ : Vec ℤ n) (agree : ∀ z → 3 ℕ.< toℕ z → oddℤ (W′ ! z) ≡ oddℤ (W ! z))
               {x y : Fin n} (x<y : x < y) (y3 : toℕ y ℕ.≤ 3) (ox : Odd (W′ ! x)) (oy : Odd (W′ ! y))
               (evl : ∀ z → toℕ z ℕ.≤ 3 → z ≢ x → z ≢ y → Even (W′ ! z)) where

    private
      x3 : toℕ x ℕ.≤ 3
      x3 = ℕP.≤-trans (ℕP.<⇒≤ x<y) y3
      ne< : ∀ {u v : Fin n} → u < v → u ≢ v
      ne< lt e = ℕP.<-irrefl (≡.cong toℕ e) lt
      oc : Odd (W′ ! c)
      oc = ≡.trans (agree c c3) (proj₁ (proj₂ (nextOdd-spec W nb)))
      od : Odd (W′ ! d)
      od = ≡.trans (agree d (ℕP.<-trans c3 c<d)) (proj₁ (proj₂ (nextOdd-spec W nc)))
      -- Beyond 3 and before c, W is even (it is even strictly between b and c).
      high : ∀ z → 3 ℕ.< toℕ z → z < c → Even (W′ ! z)
      high z h z<c = ≡.trans (agree z h) (proj₂ (proj₂ (nextOdd-spec W nb)) z (ℕP.≤-<-trans b3 h) z<c)
      -- Between y and c.
      mid : ∀ z → y < z → z < c → Even (W′ ! z)
      mid z y<z z<c = by (toℕ z ℕP.≤? 3)
        where
        by : Dec (toℕ z ℕ.≤ 3) → Even (W′ ! z)
        by (yes h) = evl z h (λ e → ne< (FinP.<-trans x<y y<z) (≡.sym e)) (λ e → ne< y<z (≡.sym e))
        by (no h) = high z (ℕP.≰⇒> h) z<c

    fo′ : firstOdd W′ ≡ just x
    fo′ = firstOdd-char W′ ox (λ z z<x → evl z (ℕP.≤-trans (ℕP.<⇒≤ z<x) x3) (ne< z<x)
                                              (ne< (FinP.<-trans z<x x<y)))
    na′ : nextOdd x W′ ≡ just y
    na′ = nextOdd-char W′ x<y oy (λ z x<z z<y → evl z (ℕP.≤-trans (ℕP.<⇒≤ z<y) y3)
                                                   (λ e → ne< x<z (≡.sym e)) (ne< z<y))
    nb′ : nextOdd y W′ ≡ just c
    nb′ = nextOdd-char W′ (low<c y3) oc mid
    nc′ : nextOdd c W′ ≡ just d
    nc′ = nextOdd-char W′ c<d od (λ z c<z z<d →
            ≡.trans (agree z (ℕP.<-trans c3 c<z)) (proj₂ (proj₂ (nextOdd-spec W nc)) z c<z z<d))

  ------------------------------------------------------------------------
  -- The six indices of Rel6

  private
    rc : ∀ {u v : Fin n} → .(u < v) → u < v
    rc {u} {v} lt = recompute (u FinP.<? v) lt

  P3<c : P3 < c
  P3<c = low<c (≤3 z3 ℕP.≤-refl)

  eQ : Emb 6 n
  eQ = emb (P0 ∷ᵛ P1 ∷ᵛ P2 ∷ᵛ P3 ∷ᵛ c ∷ᵛ d ∷ᵛ []ᵛ) (rc p01 ∷ᵢ rc p12 ∷ᵢ rc p23 ∷ᵢ P3<c ∷ᵢ c<d ∷ᵢ [ d ]ᵢ)

  -- Every index of eQ is at most p.
  ι≤p : ∀ (z : Fin 6) → lookup (P0 ∷ᵛ P1 ∷ᵛ P2 ∷ᵛ P3 ∷ᵛ c ∷ᵛ d ∷ᵛ []ᵛ) z ≤ p
  ι≤p F.zero = ℕP.≤-trans (ℕP.<⇒≤ (low<d (≤3 z0 ℕ.z≤n))) d≤p
  ι≤p (F.suc F.zero) = ℕP.≤-trans (ℕP.<⇒≤ (low<d (≤3 z1 (ℕ.s≤s ℕ.z≤n)))) d≤p
  ι≤p (F.suc (F.suc F.zero)) = ℕP.≤-trans (ℕP.<⇒≤ (low<d (≤3 z2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))) d≤p
  ι≤p (F.suc (F.suc (F.suc F.zero))) = ℕP.≤-trans (ℕP.<⇒≤ (low<d (≤3 z3 ℕP.≤-refl))) d≤p
  ι≤p (F.suc (F.suc (F.suc (F.suc F.zero)))) = ℕP.≤-trans (ℕP.<⇒≤ c<d) d≤p
  ι≤p (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))) = d≤p

  -- Lists without K.
  noK : List (Gen 6) → Bool
  noK [] = true
  noK (M-gen _ ∷ xs) = noK xs
  noK (X-gen _ _ _ ∷ xs) = noK xs
  noK (K-gen _ _ _ _ _ _ _ ∷ xs) = false

  mono-emb : (l : List (Gen 6)) → noK l ≡ true → MonoWord p ⟪ map (gen eQ) l ⟫
  mono-emb [] _ = tt
  mono-emb (M-gen x ∷ xs) h = ι≤p x , mono-emb xs h
  mono-emb (X-gen x y _ ∷ xs) h = ι≤p y , mono-emb xs h
  mono-emb (K-gen _ _ _ _ _ _ _ ∷ xs) ()

  -- K on 0, 1, 2, 3 is gK.
  k6 : Gen 6
  k6 = K-gen F.zero (F.suc F.zero) (F.suc (F.suc F.zero)) (F.suc (F.suc (F.suc F.zero)))
         (ℕ.s≤s ℕ.z≤n) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))

  -- A relation N′ K = V₁ K V₂ N of Rel6 gives the square.
  cfg-rel : (E : Eqn 6) (Np V₁ V₂ N : List (Gen 6)) → lhs E ≡ Np ++ k6 ∷ [] → rhs E ≡ V₁ ++ k6 ∷ V₂ ++ N →
            (⟪ map (gen eQ) V₁ ⟫ • ([ gK ]ʷ • ⟪ map (gen eQ) V₂ ⟫)) • ⟪ map (gen eQ) N ⟫
            ≈ ⟪ map (gen eQ) Np ⟫ • [ gK ]ʷ
  cfg-rel E Np V₁ V₂ N el er = begin
    (mV₁ • ([ gK ]ʷ • mV₂)) • mN                       ≈⟨ assoc ⟩
    mV₁ • (([ gK ]ʷ • mV₂) • mN)                       ≈⟨ cright assoc ⟩
    mV₁ • ([ gK ]ʷ • (mV₂ • mN))                       ≈⟨ cright cright sym (⟪++⟫ (map ge V₂) (map ge N)) ⟩
    mV₁ • ([ gK ]ʷ • ⟪ map ge V₂ ++ map ge N ⟫)        ≈⟨ cright cright ≡⇒≈ (≡.cong ⟪_⟫ (≡.sym (map-++ ge V₂ N))) ⟩
    mV₁ • ⟪ gK ∷ map ge (V₂ ++ N) ⟫                    ≈⟨ sym (⟪++⟫ (map ge V₁) (gK ∷ map ge (V₂ ++ N))) ⟩
    ⟪ map ge V₁ ++ map ge (k6 ∷ V₂ ++ N) ⟫             ≈⟨ ≡⇒≈ (≡.cong ⟪_⟫ (≡.sym (map-++ ge V₁ (k6 ∷ V₂ ++ N)))) ⟩
    ⟪ map ge (V₁ ++ k6 ∷ V₂ ++ N) ⟫                    ≈⟨ ≡⇒≈ (≡.cong (λ l → ⟪ map ge l ⟫) (≡.sym er)) ⟩
    ⟪ map ge (rhs E) ⟫                                 ≈⟨ sym (prf (emb⁼ eQ E)) ⟩
    ⟪ map ge (lhs E) ⟫                                 ≈⟨ ≡⇒≈ (≡.cong (λ l → ⟪ map ge l ⟫) el) ⟩
    ⟪ map ge (Np ++ k6 ∷ []) ⟫                         ≈⟨ ≡⇒≈ (≡.cong ⟪_⟫ (map-++ ge Np (k6 ∷ []))) ⟩
    ⟪ map ge Np ++ gK ∷ [] ⟫                           ≈⟨ ⟪++⟫ (map ge Np) (gK ∷ []) ⟩
    ⟪ map ge Np ⟫ • ([ gK ]ʷ • ε)                      ≈⟨ cright right-unit ⟩
    ⟪ map ge Np ⟫ • [ gK ]ʷ                            ∎
    where
    ge = gen eQ
    mV₁ = ⟪ map ge V₁ ⟫
    mV₂ = ⟪ map ge V₂ ⟫
    mN = ⟪ map ge N ⟫
    ≡⇒≈ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
    ≡⇒≈ ≡.refl = refl

  -- A normal syllable as a list.
  syl-list : ∀ (g : Gen n) (x : Fin n) (t : Bool) → ⟪ g ∷ (if t then M-gen x ∷ [] else []) ⟫ ≈ [ g ]ʷ • Mτ x t
  syl-list g x true = cright right-unit
  syl-list g x false = refl

  ------------------------------------------------------------------------
  -- Parities

  -- c + (s₁ x + s₂ y) for odd s₁, s₂.
  odd-lin2 : ∀ k s₁ s₂ x y → oddℤ s₁ ≡ true → oddℤ s₂ ≡ true →
             oddℤ (k ℤ.+ (s₁ ℤ.* x ℤ.+ s₂ ℤ.* y)) ≡ oddℤ k xor (oddℤ x xor oddℤ y)
  odd-lin2 k s₁ s₂ x y o₁ o₂ =
    ≡.trans (oddℤ-+ k _) (≡.cong (oddℤ k xor_) (≡.trans (oddℤ-+ (s₁ ℤ.* x) (s₂ ℤ.* y))
      (≡.cong₂ _xor_ (≡.trans (oddℤ-* s₁ x) (≡.cong (_∧ oddℤ x) o₁)) (≡.trans (oddℤ-* s₂ y) (≡.cong (_∧ oddℤ y) o₂)))))

  -- Shifting the first of four by κ shifts the sum by κ.
  shift4 : ∀ {A B} κ e f → A ≡ B xor κ → ((A xor e) xor f) ≡ ((B xor e) xor f) xor κ
  shift4 {B = B} κ e f ≡.refl = sh B κ e f
    where
    sh : ∀ B κ e f → (((B xor κ) xor e) xor f) ≡ ((B xor e) xor f) xor κ
    sh true true true true = ≡.refl
    sh true true true false = ≡.refl
    sh true true false true = ≡.refl
    sh true true false false = ≡.refl
    sh true false true true = ≡.refl
    sh true false true false = ≡.refl
    sh true false false true = ≡.refl
    sh true false false false = ≡.refl
    sh false true true true = ≡.refl
    sh false true true false = ≡.refl
    sh false true false true = ≡.refl
    sh false true false false = ≡.refl
    sh false false true true = ≡.refl
    sh false false true false = ≡.refl
    sh false false false true = ≡.refl
    sh false false false false = ≡.refl
