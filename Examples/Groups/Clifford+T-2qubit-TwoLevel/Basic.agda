------------------------------------------------------------------------
-- Presentations of groups
--
-- The basic generators (Lemma 3.8): X_[α,α+1], H_[0,1] and ω_[0].  Every
-- generator is relationally equal to a word of basic generators
-- (Lemma 3.8), by the conjugations
--
--   ω_[j]    = X_[0,j] ω_[0] X_[0,j]           (j > 0)
--   H_[j,l]  = X_[0,j] H_[0,l] X_[0,j]         (j > 0)
--   H_[0,l]  = X_[1,l] H_[0,1] X_[1,l]         (l > 1)
--   X_[j,l]  = X_[j,j+1] X_[j+1,l] X_[j,j+1]   (l > j + 1).
--
-- Indices are compared through toℕ, since the dimension is arbitrary.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_ ; toℕ ; fromℕ<)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; subst)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n}
  using (ω≈XωX ; H≈XHX ; H≈XHX′ ; X≈XXX ; X-X)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

------------------------------------------------------------------------
-- Basic generators

data IsBasic : Gen n → Set where
  bX : ∀ {a b} .{p : a < b} → toℕ b ≡ suc (toℕ a) → IsBasic (X-gen a b p)
  bH : ∀ {a b} .{p : a < b} → toℕ a ≡ 0 → toℕ b ≡ 1 → IsBasic (H-gen a b p)
  bω : ∀ {a} → toℕ a ≡ 0 → IsBasic (ω-gen a)

Basicʷ : Word (Gen n) → Set
Basicʷ [ g ]ʷ = IsBasic g
Basicʷ ε = ⊤
Basicʷ (u • v) = Basicʷ u × Basicʷ v

------------------------------------------------------------------------
-- Index arithmetic

private
  m<m+s : ∀ m d → m ℕ.< m ℕ.+ suc d
  m<m+s m d = subst (suc m ℕ.≤_) (≡.sym (ℕP.+-suc m d)) (s≤s (ℕP.m≤m+n m d))

  -- The index a + 1, below some index above a.
  next : (a b : Fin n) → toℕ a ℕ.< toℕ b → Fin n
  next a b a<b = fromℕ< (ℕP.≤-<-trans a<b (FinP.toℕ<n b))

  toℕ-next : ∀ a b (a<b : toℕ a ℕ.< toℕ b) → toℕ (next a b a<b) ≡ suc (toℕ a)
  toℕ-next a b a<b = FinP.toℕ-fromℕ< (ℕP.≤-<-trans a<b (FinP.toℕ<n b))

  lt-from : ∀ {a b : Fin n} d → toℕ b ≡ toℕ a ℕ.+ suc d → a < b
  lt-from {a} d e = subst (toℕ a ℕ.<_) (≡.sym e) (m<m+s (toℕ a) d)

------------------------------------------------------------------------
-- X_[j,l] as adjacent transpositions, by recursion on l - j - 1

private
  -- The data of one recursive step: j < j⁺ = j + 1 < l.
  module Split (d : ℕ) (j l : Fin n) (e : toℕ l ≡ toℕ j ℕ.+ suc (suc d)) where
    j<l : toℕ j ℕ.< toℕ l
    j<l = lt-from (suc d) e

    j⁺ : Fin n
    j⁺ = next j l j<l

    lt-next : j < j⁺
    lt-next = subst (toℕ j ℕ.<_) (≡.sym (toℕ-next j l j<l)) ℕP.≤-refl

    e′ : toℕ l ≡ toℕ j⁺ ℕ.+ suc d
    e′ = ≡.trans e (≡.trans (ℕP.+-suc (toℕ j) (suc d)) (≡.cong (ℕ._+ suc d) (≡.sym (toℕ-next j l j<l))))

    l⁺ : j⁺ < l
    l⁺ = lt-from d e′

expandX : (d : ℕ) (j l : Fin n) → toℕ l ≡ toℕ j ℕ.+ suc d → Word (Gen n)
expandX zero j l e = X j l (lt-from 0 e)
expandX (suc d) j l e = X j j⁺ lt-next • expandX d j⁺ l e′ • X j j⁺ lt-next
  where open Split d j l e

expandX-≈ : ∀ d (j l : Fin n) (e : toℕ l ≡ toℕ j ℕ.+ suc d) .(p : j < l) → X j l p ≈ expandX d j l e
expandX-≈ zero j l e p = refl
expandX-≈ (suc d) j l e p = begin
  X j l p                                               ≈⟨ X≈XXX lt-next l⁺ ⟩
  X j j⁺ lt-next • X j⁺ l l⁺ • X j j⁺ lt-next           ≈⟨ cright cleft expandX-≈ d j⁺ l e′ l⁺ ⟩
  X j j⁺ lt-next • expandX d j⁺ l e′ • X j j⁺ lt-next   ∎
  where open Split d j l e

expandX-basic : ∀ d (j l : Fin n) (e : toℕ l ≡ toℕ j ℕ.+ suc d) → Basicʷ (expandX d j l e)
expandX-basic zero j l e = bX (≡.trans e (ℕP.+-comm (toℕ j) 1))
expandX-basic (suc d) j l e = bX (toℕ-next j l j<l) , expandX-basic d j⁺ l e′ , bX (toℕ-next j l j<l)
  where open Split d j l e

------------------------------------------------------------------------
-- i_[a] and K_[a,b]

private
  -- The index 0, below any index.
  z : Fin n → Fin n
  z a = fromℕ< (ℕP.≤-<-trans z≤n (FinP.toℕ<n a))

  toℕ-z : ∀ a → toℕ (z a) ≡ 0
  toℕ-z a = FinP.toℕ-fromℕ< (ℕP.≤-<-trans z≤n (FinP.toℕ<n a))

  z<b : ∀ (a b : Fin n) m′ → toℕ b ≡ suc m′ → z a < b
  z<b a b m′ eb = subst (ℕ._< toℕ b) (≡.sym (toℕ-z a)) (subst (0 ℕ.<_) (≡.sym eb) (s≤s z≤n))

  -- toℕ a = suc m, as a distance from 0.
  from-z : ∀ (a : Fin n) m → toℕ a ≡ suc m → toℕ a ≡ toℕ (z a) ℕ.+ suc m
  from-z a m e = ≡.trans e (≡.cong (ℕ._+ suc m) (≡.sym (toℕ-z a)))

-- i_[a], given toℕ a.
expandω : (a : Fin n) (m : ℕ) → toℕ a ≡ m → Word (Gen n)
expandω a zero e = ω a
expandω a (suc m) e = expandX m (z a) a (from-z a m e) • ω (z a) • expandX m (z a) a (from-z a m e)

expandω-≈ : ∀ a m (e : toℕ a ≡ m) → ω a ≈ expandω a m e
expandω-≈ a zero e = refl
expandω-≈ a (suc m) e = begin
  ω a                                                   ≈⟨ ω≈XωX za ⟩
  X (z a) a za • ω (z a) • X (z a) a za                 ≈⟨ cong (expandX-≈ m (z a) a (from-z a m e) za)
                                                                (cright expandX-≈ m (z a) a (from-z a m e) za) ⟩
  expandX m (z a) a (from-z a m e) • ω (z a) • expandX m (z a) a (from-z a m e) ∎
  where
  za : z a < a
  za = lt-from m (from-z a m e)

expandω-basic : ∀ a m (e : toℕ a ≡ m) → Basicʷ (expandω a m e)
expandω-basic a zero e = bω e
expandω-basic a (suc m) e =
  expandX-basic m (z a) a (from-z a m e) , bω (toℕ-z a) , expandX-basic m (z a) a (from-z a m e)

-- K_[a,b] with a = 0, given toℕ b.
private
  module H₀ (a b : Fin n) (a0 : toℕ a ≡ 0) (m : ℕ) (e : toℕ b ≡ suc (suc m)) where
    a<b : toℕ a ℕ.< toℕ b
    a<b = subst₂′ a0 e
      where
      subst₂′ : toℕ a ≡ 0 → toℕ b ≡ suc (suc m) → toℕ a ℕ.< toℕ b
      subst₂′ p q = subst (ℕ._< toℕ b) (≡.sym p) (subst (0 ℕ.<_) (≡.sym q) (s≤s z≤n))

    one : Fin n
    one = next a b a<b

    toℕ-one : toℕ one ≡ 1
    toℕ-one = ≡.trans (toℕ-next a b a<b) (≡.cong suc a0)

    a<one : a < one
    a<one = subst (toℕ a ℕ.<_) (≡.sym (toℕ-next a b a<b)) ℕP.≤-refl

    e′ : toℕ b ≡ toℕ one ℕ.+ suc m
    e′ = ≡.trans e (≡.cong (ℕ._+ suc m) (≡.sym toℕ-one))

    one<b : one < b
    one<b = lt-from m e′

expandH₀ : (a b : Fin n) → toℕ a ≡ 0 → (m : ℕ) → toℕ b ≡ suc m → .(a < b) → Word (Gen n)
expandH₀ a b a0 zero e p = H a b p
expandH₀ a b a0 (suc m) e p = expandX m one b e′ • H a one a<one • expandX m one b e′
  where open H₀ a b a0 m e

expandH₀-≈ : ∀ a b (a0 : toℕ a ≡ 0) m (e : toℕ b ≡ suc m) .(p : a < b) → H a b p ≈ expandH₀ a b a0 m e p
expandH₀-≈ a b a0 zero e p = refl
expandH₀-≈ a b a0 (suc m) e p = begin
  H a b p                                             ≈⟨ H≈XHX′ a<one one<b ⟩
  X one b one<b • H a one a<one • X one b one<b       ≈⟨ cong (expandX-≈ m one b e′ one<b) (cright expandX-≈ m one b e′ one<b) ⟩
  expandX m one b e′ • H a one a<one • expandX m one b e′ ∎
  where open H₀ a b a0 m e

expandH₀-basic : ∀ a b (a0 : toℕ a ≡ 0) m (e : toℕ b ≡ suc m) .(p : a < b) → Basicʷ (expandH₀ a b a0 m e p)
expandH₀-basic a b a0 zero e p = bH a0 e
expandH₀-basic a b a0 (suc m) e p = expandX-basic m one b e′ , bH a0 toℕ-one , expandX-basic m one b e′
  where open H₀ a b a0 m e

-- K_[a,b], given toℕ a and toℕ b.
expandH : (a b : Fin n) (m : ℕ) → toℕ a ≡ m → (m′ : ℕ) → toℕ b ≡ suc m′ → .(a < b) → Word (Gen n)
expandH a b zero ea m′ eb p = expandH₀ a b ea m′ eb p
expandH a b (suc m) ea m′ eb p =
  expandX m (z a) a (from-z a m ea) • expandH₀ (z a) b (toℕ-z a) m′ eb (z<b a b m′ eb) • expandX m (z a) a (from-z a m ea)

expandH-≈ : ∀ a b m (ea : toℕ a ≡ m) m′ (eb : toℕ b ≡ suc m′) .(p : a < b) → H a b p ≈ expandH a b m ea m′ eb p
expandH-≈ a b zero ea m′ eb p = expandH₀-≈ a b ea m′ eb p
expandH-≈ a b (suc m) ea m′ eb p = begin
  H a b p                                                 ≈⟨ H≈XHX za (recompute (a FinP.<? b) p) ⟩
  X (z a) a za • H (z a) b (z<b a b m′ eb) • X (z a) a za ≈⟨ cong (expandX-≈ m (z a) a (from-z a m ea) za)
                                                                  (cong (expandH₀-≈ (z a) b (toℕ-z a) m′ eb (z<b a b m′ eb))
                                                                        (expandX-≈ m (z a) a (from-z a m ea) za)) ⟩
  expandH a b (suc m) ea m′ eb p                          ∎
  where
  za : z a < a
  za = lt-from m (from-z a m ea)

------------------------------------------------------------------------
-- Every generator, and every word

private
  rc : {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} p = recompute (a FinP.<? b) p

  gap : ∀ (a b : Fin n) → a < b → toℕ b ≡ toℕ a ℕ.+ suc (toℕ b ℕ.∸ suc (toℕ a))
  gap a b lt = ≡.trans (≡.sym (ℕP.m+[n∸m]≡n lt)) (≡.sym (ℕP.+-suc (toℕ a) (toℕ b ℕ.∸ suc (toℕ a))))

  -- toℕ b = suc m for some m.
  pos : ∀ (x : ℕ) → 0 ℕ.< x → ∃ λ m → x ≡ suc m
  pos (suc m) _ = m , ≡.refl

  above : ∀ {a b : Fin n} → a < b → 0 ℕ.< toℕ b
  above {a} lt = ℕP.≤-trans (s≤s z≤n) lt

expandH-basic : ∀ a b m (ea : toℕ a ≡ m) m′ (eb : toℕ b ≡ suc m′) .(p : a < b) → Basicʷ (expandH a b m ea m′ eb p)
expandH-basic a b zero ea m′ eb p = expandH₀-basic a b ea m′ eb p
expandH-basic a b (suc m) ea m′ eb p =
  expandX-basic m (z a) a (from-z a m ea) , expandH₀-basic (z a) b (toℕ-z a) m′ eb (z<b a b m′ eb) ,
  expandX-basic m (z a) a (from-z a m ea)

expand : Gen n → Word (Gen n)
expand (X-gen a b p) = expandX (toℕ b ℕ.∸ suc (toℕ a)) a b (gap a b (rc p))
expand (H-gen a b p) = expandH a b (toℕ a) ≡.refl (proj₁ s) (proj₂ s) p
  where s = pos (toℕ b) (above (rc p))
expand (ω-gen a) = expandω a (toℕ a) ≡.refl

expand-≈ : (g : Gen n) → [ g ]ʷ ≈ expand g
expand-≈ (X-gen a b p) = expandX-≈ (toℕ b ℕ.∸ suc (toℕ a)) a b (gap a b (rc p)) p
expand-≈ (H-gen a b p) = expandH-≈ a b (toℕ a) ≡.refl (proj₁ s) (proj₂ s) p
  where s = pos (toℕ b) (above (rc p))
expand-≈ (ω-gen a) = expandω-≈ a (toℕ a) ≡.refl

-- Words
expandʷ : Word (Gen n) → Word (Gen n)
expandʷ = expand ʷ

expandʷ-≈ : (w : Word (Gen n)) → w ≈ expandʷ w
expandʷ-≈ [ g ]ʷ = expand-≈ g
expandʷ-≈ ε = refl
expandʷ-≈ (u • v) = cong (expandʷ-≈ u) (expandʷ-≈ v)

expand-basic : (g : Gen n) → Basicʷ (expand g)
expand-basic (X-gen a b p) = expandX-basic (toℕ b ℕ.∸ suc (toℕ a)) a b (gap a b (rc p))
expand-basic (H-gen a b p) = expandH-basic a b (toℕ a) ≡.refl (proj₁ s) (proj₂ s) p
  where s = pos (toℕ b) (above (rc p))
expand-basic (ω-gen a) = expandω-basic a (toℕ a) ≡.refl

expandʷ-basic : (w : Word (Gen n)) → Basicʷ (expandʷ w)
expandʷ-basic [ g ]ʷ = expand-basic g
expandʷ-basic ε = tt
expandʷ-basic (u • v) = expandʷ-basic u , expandʷ-basic v

------------------------------------------------------------------------
-- The shape of the expansions, for the level argument (Levels)

-- Every letter is X_[a,c] or i_[c] with c ≤ l.
Letters≤ : Fin n → Word (Gen n) → Set
Letters≤ l [ X-gen a c _ ]ʷ = toℕ c ℕ.≤ toℕ l
Letters≤ l [ H-gen _ _ _ ]ʷ = ⊥
Letters≤ l [ ω-gen c ]ʷ = toℕ c ℕ.≤ toℕ l
Letters≤ l ε = ⊤
Letters≤ l (u • v) = Letters≤ l u × Letters≤ l v

Letters≤-weaken : ∀ {l l′} (w : Word (Gen n)) → toℕ l ℕ.≤ toℕ l′ → Letters≤ l w → Letters≤ l′ w
Letters≤-weaken [ X-gen a c _ ]ʷ ll′ h = ℕP.≤-trans h ll′
Letters≤-weaken [ ω-gen c ]ʷ ll′ h = ℕP.≤-trans h ll′
Letters≤-weaken ε ll′ _ = tt
Letters≤-weaken (u • v) ll′ (hu , hv) = Letters≤-weaken u ll′ hu , Letters≤-weaken v ll′ hv

-- An H expansion: a single H, or a conjugate by an involution P of
-- transpositions.
data HShape (b : Fin n) : Word (Gen n) → Set where
  single   : ∀ {a c} .{p : a < c} → toℕ c ℕ.≤ toℕ b → HShape b (H a c p)
  sandwich : ∀ {P Y} → Letters≤ b P → P • P ≈ ε → HShape b Y → HShape b (P • Y • P)

expandX-letters : ∀ d (j l : Fin n) (e : toℕ l ≡ toℕ j ℕ.+ suc d) → Letters≤ l (expandX d j l e)
expandX-letters zero j l e = ℕP.≤-refl
expandX-letters (suc d) j l e = ℕP.<⇒≤ l⁺ , expandX-letters d j⁺ l e′ , ℕP.<⇒≤ l⁺
  where open Split d j l e

expandX-inv : ∀ d (j l : Fin n) (e : toℕ l ≡ toℕ j ℕ.+ suc d) → expandX d j l e • expandX d j l e ≈ ε
expandX-inv d j l e =
  trans (cong (sym (expandX-≈ d j l e (lt-from d e))) (sym (expandX-≈ d j l e (lt-from d e)))) (X-X (lt-from d e))

expandω-letters : ∀ (a : Fin n) m (e : toℕ a ≡ m) → Letters≤ a (expandω a m e)
expandω-letters a zero e = ℕP.≤-refl
expandω-letters a (suc m) e =
  expandX-letters m (z a) a (from-z a m e) ,
  subst (ℕ._≤ toℕ a) (≡.sym (toℕ-z a)) z≤n ,
  expandX-letters m (z a) a (from-z a m e)

expandH₀-shape : ∀ (a b : Fin n) (a0 : toℕ a ≡ 0) m (e : toℕ b ≡ suc m) .(p : a < b) → HShape b (expandH₀ a b a0 m e p)
expandH₀-shape a b a0 zero e p = single ℕP.≤-refl
expandH₀-shape a b a0 (suc m) e p =
  sandwich (expandX-letters m one b e′) (expandX-inv m one b e′) (single (ℕP.<⇒≤ one<b))
  where open H₀ a b a0 m e

expandH-shape : ∀ (a b : Fin n) m (ea : toℕ a ≡ m) m′ (eb : toℕ b ≡ suc m′) .(p : a < b) →
                HShape b (expandH a b m ea m′ eb p)
expandH-shape a b zero ea m′ eb p = expandH₀-shape a b ea m′ eb p
expandH-shape a b (suc m) ea m′ eb p =
  sandwich (Letters≤-weaken (expandX m (z a) a (from-z a m ea)) (ℕP.<⇒≤ (recompute (a FinP.<? b) p))
                            (expandX-letters m (z a) a (from-z a m ea)))
           (expandX-inv m (z a) a (from-z a m ea))
           (expandH₀-shape (z a) b (toℕ-z a) m′ eb (z<b a b m′ eb))

-- For each kind of generator.
expand-letters-X : ∀ (a b : Fin n) .(p : a < b) → Letters≤ b (expand (X-gen a b p))
expand-letters-X a b p = expandX-letters (toℕ b ℕ.∸ suc (toℕ a)) a b (gap a b (rc p))

expand-letters-ω : ∀ (a : Fin n) → Letters≤ a (expand (ω-gen a))
expand-letters-ω a = expandω-letters a (toℕ a) ≡.refl

expand-shape-H : ∀ (a b : Fin n) .(p : a < b) → HShape b (expand (H-gen a b p))
expand-shape-H a b p = expandH-shape a b (toℕ a) ≡.refl (proj₁ s) (proj₂ s) p
  where s = pos (toℕ b) (above (rc p))
