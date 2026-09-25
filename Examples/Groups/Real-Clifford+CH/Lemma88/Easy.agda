------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on the rules of Figure 8 whose decodings agree by
-- definition (Clément, Appendix E.5)
--
-- The paper disposes of a dozen of the twenty-seven rules in a line
-- each, "from the definition": here (20), (21), (25)–(28), (30), (33),
-- (34), (35) and (42).  `dZZ` is trivial on one index and symmetric; `dZX` decides
-- whether its first index is the lower or the upper one of the pair, or
-- neither ((30)), and the recursions (25)–(28) are the clauses of
-- `dZXlo`/`dZXhi` for the parity of the gap; `dXX` is (34).  Each
-- computation is stated on the natural-number indices (`D25` …), the
-- rule itself on the letters.  d reverses D, so every rule comes out
-- reversed, which association absorbs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Lemma88.Easy (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; if_then_else_ ; _∧_)
open import Data.Bool.Properties using (not-involutive)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ<) renaming (_≟_ to _≟F_)
open import Data.Nat using (zero ; suc ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<ᵇ_ ; _≡ᵇ_ ; s≤s ; z≤n ; _^_)
open import Data.Nat.Properties using (n∸n≡0 ; <⇒≤ ; <-cmp ; n<1+n ; <⇒≢ ; +-suc ; m+n∸m≡n ; m+[n∸m]≡n ; ≤-trans ; n≤1+n ; ≤-refl)
open import Data.Maybe using (just ; nothing)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (parity ; code ; toBits ; gray ; hd ; 8≤2^)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Small using (Small ; small)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃ ; hhℕ-hh)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HLetters using (hpat-flips)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; −1−1 ; −1X ; XX ; HH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (Succ)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (zz ; zx ; xx ; hh ; hhℕ ; zxℕ ; Σ ; Σ′ ; distinct4 ; twoSmallest ; hpat ; toFin)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dZZ ; dZZ-chain ; dZX ; dZXb ; dZXs ; dZXself ; dZXlo ; dZXhi ; dZXlo₁ ; dZXhi₁ ; dXX ;
         dHH ; dHH₄ ; dHH₄-pat ; dHH₄-nopat ; dΣ ; gadget ; gcode)

private
  N : ℕ
  N = ₃₊ m

  I : Set
  I = Fin (2 ^ N)

------------------------------------------------------------------------
-- Comparisons

private
  lt-true : ∀ a b → a < b → (a <ᵇ b) ≡ true
  lt-true a       zero    ()
  lt-true zero    (suc b) _       = Eq.refl
  lt-true (suc a) (suc b) (s≤s p) = lt-true a b p

  ge-false : ∀ a b → b ≤ a → (a <ᵇ b) ≡ false
  ge-false a       zero    _       = Eq.refl
  ge-false zero    (suc b) ()
  ge-false (suc a) (suc b) (s≤s p) = ge-false a b p

  ≡ᵇ-refl : ∀ x → (x ≡ᵇ x) ≡ true
  ≡ᵇ-refl zero    = Eq.refl
  ≡ᵇ-refl (suc x) = ≡ᵇ-refl x

  ≡ᵇ-≢ : ∀ x y → x ≢ y → (x ≡ᵇ y) ≡ false
  ≡ᵇ-≢ zero    zero    ne = ⊥-elim (ne Eq.refl)
  ≡ᵇ-≢ zero    (suc y) _  = Eq.refl
  ≡ᵇ-≢ (suc x) zero    _  = Eq.refl
  ≡ᵇ-≢ (suc x) (suc y) ne = ≡ᵇ-≢ x y (λ e → ne (Eq.cong suc e))

  sx∸x : ∀ x → suc x ∸ x ≡ 1
  sx∸x zero    = Eq.refl
  sx∸x (suc x) = sx∸x x

  -- The gap between two indices at least two apart.
  gap : ∀ x y → suc (suc x) ≤ y → Σ[ k ∈ ℕ ] (y ∸ x ≡ suc (suc k)) × (y ∸ suc x ≡ suc k)
  gap zero    (suc (suc k)) (s≤s (s≤s _)) = k , Eq.refl , Eq.refl
  gap (suc x) (suc y)       (s≤s p)       = gap x y p

  parity² : ∀ k → parity (suc (suc k)) ≡ parity k
  parity² k = not-involutive (parity k)

  -- x + (1 + k) is the index just below x + (2 + k).
  top∸ : ∀ x k → suc (x + suc k) ∸ x ≡ suc (suc k)
  top∸ x k = Eq.trans (Eq.cong (_∸ x) (Eq.sym (+-suc x (suc k)))) (m+n∸m≡n x (suc (suc k)))

  lt-top : ∀ x k → x < x + suc k
  lt-top zero    k = s≤s z≤n
  lt-top (suc x) k = s≤s (lt-top x k)

  ne-ℕ : ∀ {a b : I} → toℕ a ≢ toℕ b → a ≢ b
  ne-ℕ ne e = ne (Eq.cong toℕ e)

------------------------------------------------------------------------
-- The decoding of the signs and of the signed exchanges, computed

private
  dZZ-lt : ∀ {x y} → x < y → dZZ {m} x y ≡ dZZ-chain x (y ∸ x)
  dZZ-lt {x} {y} p = Eq.cong (λ β → if β then dZZ-chain {m} x (y ∸ x) else dZZ-chain y (x ∸ y)) (lt-true x y p)

  dZZ-ge : ∀ {x y} → y ≤ x → dZZ {m} x y ≡ dZZ-chain y (x ∸ y)
  dZZ-ge {x} {y} p = Eq.cong (λ β → if β then dZZ-chain {m} x (y ∸ x) else dZZ-chain y (x ∸ y)) (ge-false x y p)

dZZ-self : ∀ x → dZZ {m} x x ≡ ε
dZZ-self x = Eq.trans (dZZ-ge ≤-refl) (Eq.cong (dZZ-chain x) (n∸n≡0 x))

dZZ-sym : ∀ x y → dZZ {m} x y ≡ dZZ y x
dZZ-sym x y with <-cmp x y
... | tri< p _ _      = Eq.trans (dZZ-lt p) (Eq.sym (dZZ-ge (<⇒≤ p)))
... | tri≈ _ Eq.refl _ = Eq.refl
... | tri> _ _ p      = Eq.trans (dZZ-ge (<⇒≤ p)) (Eq.sym (dZZ-lt p))

private
  -- The index c is the lower one of the pair.
  dZX-lo : ∀ {x y} → x < y → dZX {m} x x y ≡ dZXlo x (y ∸ x)
  dZX-lo {x} {y} p = Eq.trans (Eq.cong (λ β → dZXb {m} β x x y) (lt-true x y p))
                              (Eq.cong (λ e → dZXs {m} e (x ≡ᵇ y) x y x y x) (≡ᵇ-refl x))

  dZX-lo′ : ∀ {x y} → x < y → dZX {m} x y x ≡ dZXlo x (y ∸ x)
  dZX-lo′ {x} {y} p = Eq.trans (Eq.cong (λ β → dZXb {m} β x y x) (ge-false y x (<⇒≤ p)))
                               (Eq.cong (λ e → dZXs {m} e (x ≡ᵇ y) x y y x x) (≡ᵇ-refl x))

  -- The upper one.
  dZX-hi : ∀ {x y} → x < y → dZX {m} y x y ≡ dZXhi x (y ∸ x)
  dZX-hi {x} {y} p = Eq.trans (Eq.cong (λ β → dZXb {m} β y x y) (lt-true x y p))
                              (Eq.cong₂ (λ e₁ e₂ → dZXs {m} e₁ e₂ x y x y y)
                                        (≡ᵇ-≢ y x (λ e → <⇒≢ p (Eq.sym e))) (≡ᵇ-refl y))

  dZX-hi′ : ∀ {x y} → x < y → dZX {m} y y x ≡ dZXhi x (y ∸ x)
  dZX-hi′ {x} {y} p = Eq.trans (Eq.cong (λ β → dZXb {m} β y y x) (ge-false y x (<⇒≤ p)))
                               (Eq.cong₂ (λ e₁ e₂ → dZXs {m} e₁ e₂ x y y x y)
                                         (≡ᵇ-≢ y x (λ e → <⇒≢ p (Eq.sym e))) (≡ᵇ-refl y))

  -- Neither.
  dZX-mid : ∀ c a b → c ≢ a → c ≢ b → dZX {m} c a b ≡ dZXself a b • dZZ c a
  dZX-mid c a b ca cb = mid (a <ᵇ b)
    where
    mid : ∀ β → dZXb {m} β c a b ≡ dZXself a b • dZZ c a
    mid true  = Eq.cong₂ (λ e₁ e₂ → dZXs {m} e₁ e₂ a b a b c) (≡ᵇ-≢ c a ca) (≡ᵇ-≢ c b cb)
    mid false = Eq.cong₂ (λ e₁ e₂ → dZXs {m} e₁ e₂ b a a b c) (≡ᵇ-≢ c b cb) (≡ᵇ-≢ c a ca)

  -- (−1)_[a] X_[a,b] is the exchange of a, b signed on a.
  dZX-self : ∀ {x y} → x ≢ y → dZX {m} x x y ≡ dZXself x y
  dZX-self {x} {y} xy with <-cmp x y
  ... | tri< p _ _ = Eq.trans (dZX-lo p)
                       (Eq.sym (Eq.cong (λ β → if β then dZXlo {m} x (y ∸ x) else dZXhi y (x ∸ y)) (lt-true x y p)))
  ... | tri≈ _ e _ = ⊥-elim (xy e)
  ... | tri> _ _ p = Eq.trans (Eq.trans (Eq.cong (λ β → dZXb {m} β x x y) (ge-false x y (<⇒≤ p)))
                                        (Eq.cong₂ (λ e₁ e₂ → dZXs {m} e₁ e₂ y x x y x)
                                                  (≡ᵇ-≢ x y xy) (≡ᵇ-refl x)))
                       (Eq.sym (Eq.cong (λ β → if β then dZXlo {m} x (y ∸ x) else dZXhi y (x ∸ y))
                                        (ge-false x y (<⇒≤ p))))

  -- The recursions of Definition 8.3, by the parity of the gap.
  lo-even : ∀ a k → parity k ≡ true → dZXlo {m} a (suc (suc k)) ≡ dZXlo₁ a • dZXlo (suc a) (suc k) • dZXhi₁ a
  lo-even a k e = Eq.cong (λ β → if β then dZXlo₁ {m} a • dZXlo (suc a) (suc k) • dZXhi₁ a
                                 else dZXhi₁ (a + suc k) • dZXlo a (suc k) • dZXlo₁ (a + suc k)) e

  lo-odd : ∀ a k → parity k ≡ false → dZXlo {m} a (suc (suc k)) ≡ dZXhi₁ (a + suc k) • dZXlo a (suc k) • dZXlo₁ (a + suc k)
  lo-odd a k e = Eq.cong (λ β → if β then dZXlo₁ {m} a • dZXlo (suc a) (suc k) • dZXhi₁ a
                                else dZXhi₁ (a + suc k) • dZXlo a (suc k) • dZXlo₁ (a + suc k)) e

  hi-even : ∀ a k → parity k ≡ true → dZXhi {m} a (suc (suc k)) ≡ dZXlo₁ a • dZXhi (suc a) (suc k) • dZXhi₁ a
  hi-even a k e = Eq.cong (λ β → if β then dZXlo₁ {m} a • dZXhi (suc a) (suc k) • dZXhi₁ a
                                 else dZXhi₁ (a + suc k) • dZXhi a (suc k) • dZXlo₁ (a + suc k)) e

  hi-odd : ∀ a k → parity k ≡ false → dZXhi {m} a (suc (suc k)) ≡ dZXhi₁ (a + suc k) • dZXhi a (suc k) • dZXlo₁ (a + suc k)
  hi-odd a k e = Eq.cong (λ β → if β then dZXlo₁ {m} a • dZXhi (suc a) (suc k) • dZXhi₁ a
                                else dZXhi₁ (a + suc k) • dZXhi a (suc k) • dZXlo₁ (a + suc k)) e

  -- The exchange of consecutive indices.
  lo₁≡ : ∀ x → dZX {m} x x (suc x) ≡ dZXlo₁ x
  lo₁≡ x = Eq.trans (dZX-lo (n<1+n x)) (Eq.cong (dZXlo x) (sx∸x x))

  hi₁≡ : ∀ x → dZX {m} (suc x) x (suc x) ≡ dZXhi₁ x
  hi₁≡ x = Eq.trans (dZX-hi (n<1+n x)) (Eq.cong (dZXhi x) (sx∸x x))

------------------------------------------------------------------------
-- The letters

zx-letter : ∀ (c a b : I) (ab : a ≢ b) → zx {N} c a b ≡ [ −1X c a b ab ]ʷ
zx-letter c a b ab with a ≟F b
... | yes e = ⊥-elim (ab e)
... | no _  = Eq.refl

zx-same : ∀ (c a : I) → zx {N} c a a ≡ ε
zx-same c a with a ≟F a
... | yes _ = Eq.refl
... | no ne = ⊥-elim (ne Eq.refl)

xx-letter : ∀ (a b c e : I) (ab : a ≢ b) (ce : c ≢ e) → xx {N} a b c e ≡ [ XX a b c e ab ce ]ʷ
xx-letter a b c e ab ce with a ≟F b | c ≟F e
... | yes p | _     = ⊥-elim (ab p)
... | no _  | yes p = ⊥-elim (ce p)
... | no _  | no _  = Eq.refl

d-zx : ∀ (c a b : I) → a ≢ b → (d ʷ) (zx {N} c a b) ≡ rev (dZX {m} (toℕ c) (toℕ a) (toℕ b))
d-zx c a b ab = Eq.cong (d ʷ) (zx-letter c a b ab)

------------------------------------------------------------------------
-- The rules

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

-- (20)
e20 : ∀ (a : I) → (d ʷ) (zz {N} a a) ≈ ε
e20 a = ≡→≈ (Eq.cong rev (dZZ-self (toℕ a)))

-- (21)
e21 : ∀ (a b : I) → (d ʷ) (zz {N} a b) ≈ (d ʷ) (zz b a)
e21 a b = ≡→≈ (Eq.cong rev (dZZ-sym (toℕ a) (toℕ b)))


private
  suc∸ : ∀ x y → x ≤ y → suc y ∸ x ≡ suc (y ∸ x)
  suc∸ zero    y       _       = Eq.refl
  suc∸ (suc x) (suc y) (s≤s p) = suc∸ x y p

  rev3 : ∀ (u v w : Circuit N) → rev (u • v • w) ≈ rev w • rev v • rev u
  rev3 u v w = assoc

-- (25) and (26) on the indices: the gap y − x is even, k is it less two.
D25 : ∀ x y k → suc (suc x) ≤ y → y ∸ x ≡ suc (suc k) → y ∸ suc x ≡ suc k → parity k ≡ true →
      rev (dZX {m} x x y) ≈ rev (dZX (suc x) x (suc x)) • rev (dZX (suc x) (suc x) y) • rev (dZX x x (suc x))
D25 x y k p e₁ e₂ par =
  trans (≡→≈ (Eq.cong rev (Eq.trans (dZX-lo (≤-trans (n≤1+n _) p))
                                    (Eq.trans (Eq.cong (dZXlo x) e₁) (lo-even x k par)))))
        (trans (rev3 (dZXlo₁ x) (dZXlo (suc x) (suc k)) (dZXhi₁ x))
               (≡→≈ (Eq.sym (Eq.cong₂ (λ u v → rev u • v) (hi₁≡ x)
                               (Eq.cong₂ (λ v w → rev v • rev w)
                                         (Eq.trans (dZX-lo p) (Eq.cong (dZXlo (suc x)) e₂)) (lo₁≡ x))))))

D26 : ∀ x y k → suc (suc x) ≤ y → y ∸ x ≡ suc (suc k) → y ∸ suc x ≡ suc k → parity k ≡ true →
      rev (dZX {m} y x y) ≈ rev (dZX (suc x) x (suc x)) • rev (dZX y (suc x) y) • rev (dZX x x (suc x))
D26 x y k p e₁ e₂ par =
  trans (≡→≈ (Eq.cong rev (Eq.trans (dZX-hi (≤-trans (n≤1+n _) p))
                                    (Eq.trans (Eq.cong (dZXhi x) e₁) (hi-even x k par)))))
        (trans (rev3 (dZXlo₁ x) (dZXhi (suc x) (suc k)) (dZXhi₁ x))
               (≡→≈ (Eq.sym (Eq.cong₂ (λ u v → rev u • v) (hi₁≡ x)
                               (Eq.cong₂ (λ v w → rev v • rev w)
                                         (Eq.trans (dZX-hi p) (Eq.cong (dZXhi (suc x)) e₂)) (lo₁≡ x))))))

-- (27) and (28): the gap is odd; y′ is the upper index less one.
D27 : ∀ x y′ k → x < y′ → y′ ∸ x ≡ suc k → y′ ≡ x + suc k → parity k ≡ false →
      rev (dZX {m} x x (suc y′)) ≈ rev (dZX y′ y′ (suc y′)) • rev (dZX x x y′) • rev (dZX (suc y′) y′ (suc y′))
D27 x y′ k p e₁ e₂ par =
  trans (≡→≈ (Eq.cong rev (Eq.trans (dZX-lo (≤-trans p (n≤1+n _)))
                                    (Eq.trans (Eq.cong (dZXlo x) (Eq.trans (suc∸ x y′ (<⇒≤ p)) (Eq.cong suc e₁)))
                                    (Eq.trans (lo-odd x k par)
                                              (Eq.cong (λ t → dZXhi₁ t • dZXlo x (suc k) • dZXlo₁ t) (Eq.sym e₂)))))))
        (trans (rev3 (dZXhi₁ y′) (dZXlo x (suc k)) (dZXlo₁ y′))
               (≡→≈ (Eq.sym (Eq.cong₂ (λ u v → rev u • v) (lo₁≡ y′)
                               (Eq.cong₂ (λ v w → rev v • rev w)
                                         (Eq.trans (dZX-lo p) (Eq.cong (dZXlo x) e₁)) (hi₁≡ y′))))))

D28 : ∀ x y′ k → x < y′ → y′ ∸ x ≡ suc k → y′ ≡ x + suc k → parity k ≡ false →
      rev (dZX {m} (suc y′) x (suc y′)) ≈ rev (dZX y′ y′ (suc y′)) • rev (dZX y′ x y′) • rev (dZX (suc y′) y′ (suc y′))
D28 x y′ k p e₁ e₂ par =
  trans (≡→≈ (Eq.cong rev (Eq.trans (dZX-hi (≤-trans p (n≤1+n _)))
                                    (Eq.trans (Eq.cong (dZXhi x) (Eq.trans (suc∸ x y′ (<⇒≤ p)) (Eq.cong suc e₁)))
                                    (Eq.trans (hi-odd x k par)
                                              (Eq.cong (λ t → dZXhi₁ t • dZXhi x (suc k) • dZXlo₁ t) (Eq.sym e₂)))))))
        (trans (rev3 (dZXhi₁ y′) (dZXhi x (suc k)) (dZXlo₁ y′))
               (≡→≈ (Eq.sym (Eq.cong₂ (λ u v → rev u • v) (lo₁≡ y′)
                               (Eq.cong₂ (λ v w → rev v • rev w)
                                         (Eq.trans (dZX-hi p) (Eq.cong (dZXhi x) e₁)) (hi₁≡ y′))))))

------------------------------------------------------------------------
-- The rules on the letters

private
  -- The odd gap, read off the hypotheses of (27) and (28).
  odd-gap : ∀ x y′ → suc x < suc y′ →
            Σ[ k ∈ ℕ ] (x < y′) × (y′ ∸ x ≡ suc k) × (y′ ≡ x + suc k) × (suc y′ ∸ x ≡ suc (suc k))
  odd-gap x y′ (s≤s p) with gap x (suc y′) (s≤s p)
  ... | k , e₁ , e₂ = k , p , e₂ , Eq.trans (Eq.sym (m+[n∸m]≡n (<⇒≤ p))) (Eq.cong (x +_) e₂) , e₁

  par-of : ∀ {y x k b} → y ∸ x ≡ suc (suc k) → parity (y ∸ x) ≡ b → parity k ≡ b
  par-of {k = k} e q = Eq.trans (Eq.sym (parity² k)) (Eq.trans (Eq.cong parity (Eq.sym e)) q)

-- (25)
e25 : ∀ (a a′ c : I) → Succ a a′ → toℕ a′ < toℕ c → parity (toℕ c ∸ toℕ a) ≡ true →
      (d ʷ) (zx {N} a a c) ≈ (d ʷ) (zx a′ a a′ • zx a′ a′ c • zx a a a′)
e25 a a′ c s p q with gap (toℕ a) (toℕ c) (Eq.subst (λ t → suc t ≤ toℕ c) s p)
... | k , e₁ , e₂ =
  trans (≡→≈ (d-zx a a c (ne-ℕ (<⇒≢ (≤-trans (n≤1+n _) p′)))))
        (trans (D25 x y k p′ e₁ e₂ (par-of e₁ q)) (≡→≈ (Eq.sym rhs)))
  where
  x y : ℕ
  x = toℕ a
  y = toℕ c
  p′ : suc (suc x) ≤ y
  p′ = Eq.subst (λ t → suc t ≤ y) s p
  aa′ : a ≢ a′
  aa′ = ne-ℕ (λ e → <⇒≢ (n<1+n x) (Eq.trans e s))
  rhs : (d ʷ) (zx {N} a′ a a′ • zx a′ a′ c • zx a a a′) ≡
        rev (dZX {m} (suc x) x (suc x)) • rev (dZX (suc x) (suc x) y) • rev (dZX x x (suc x))
  rhs = Eq.trans (Eq.cong₂ _•_ (d-zx a′ a a′ aa′) (Eq.cong₂ _•_ (d-zx a′ a′ c (ne-ℕ (<⇒≢ p))) (d-zx a a a′ aa′)))
                 (Eq.cong (λ t → rev (dZX {m} t x t) • rev (dZX t t y) • rev (dZX x x t)) s)

-- (26)
e26 : ∀ (a a′ c : I) → Succ a a′ → toℕ a′ < toℕ c → parity (toℕ c ∸ toℕ a) ≡ true →
      (d ʷ) (zx {N} c a c) ≈ (d ʷ) (zx a′ a a′ • zx c a′ c • zx a a a′)
e26 a a′ c s p q with gap (toℕ a) (toℕ c) (Eq.subst (λ t → suc t ≤ toℕ c) s p)
... | k , e₁ , e₂ =
  trans (≡→≈ (d-zx c a c (ne-ℕ (<⇒≢ (≤-trans (n≤1+n _) p′)))))
        (trans (D26 x y k p′ e₁ e₂ (par-of e₁ q)) (≡→≈ (Eq.sym rhs)))
  where
  x y : ℕ
  x = toℕ a
  y = toℕ c
  p′ : suc (suc x) ≤ y
  p′ = Eq.subst (λ t → suc t ≤ y) s p
  aa′ : a ≢ a′
  aa′ = ne-ℕ (λ e → <⇒≢ (n<1+n x) (Eq.trans e s))
  rhs : (d ʷ) (zx {N} a′ a a′ • zx c a′ c • zx a a a′) ≡
        rev (dZX {m} (suc x) x (suc x)) • rev (dZX y (suc x) y) • rev (dZX x x (suc x))
  rhs = Eq.trans (Eq.cong₂ _•_ (d-zx a′ a a′ aa′) (Eq.cong₂ _•_ (d-zx c a′ c (ne-ℕ (<⇒≢ p))) (d-zx a a a′ aa′)))
                 (Eq.cong (λ t → rev (dZX {m} t x t) • rev (dZX y t y) • rev (dZX x x t)) s)

-- (27)
e27 : ∀ (a c′ c : I) → Succ c′ c → suc (toℕ a) < toℕ c → parity (toℕ c ∸ toℕ a) ≡ false →
      (d ʷ) (zx {N} a a c) ≈ (d ʷ) (zx c′ c′ c • zx a a c′ • zx c c′ c)
e27 a c′ c s p q with odd-gap (toℕ a) (toℕ c′) (Eq.subst (λ t → suc (toℕ a) < t) s p)
... | k , xy′ , e₁ , e₂ , e₃ =
  trans (≡→≈ (Eq.trans (d-zx a a c (ne-ℕ (<⇒≢ (≤-trans (n≤1+n _) p))))
                       (Eq.cong (λ t → rev (dZX {m} x x t)) s)))
        (trans (D27 x y′ k xy′ e₁ e₂ (par-of e₃ (Eq.subst (λ t → parity (t ∸ x) ≡ false) s q)))
               (≡→≈ (Eq.sym rhs)))
  where
  x y′ : ℕ
  x  = toℕ a
  y′ = toℕ c′
  c′c : c′ ≢ c
  c′c = ne-ℕ (λ e → <⇒≢ (n<1+n y′) (Eq.trans e s))
  rhs : (d ʷ) (zx {N} c′ c′ c • zx a a c′ • zx c c′ c) ≡
        rev (dZX {m} y′ y′ (suc y′)) • rev (dZX x x y′) • rev (dZX (suc y′) y′ (suc y′))
  rhs = Eq.trans (Eq.cong₂ _•_ (d-zx c′ c′ c c′c) (Eq.cong₂ _•_ (d-zx a a c′ (ne-ℕ (<⇒≢ xy′))) (d-zx c c′ c c′c)))
                 (Eq.cong (λ t → rev (dZX {m} y′ y′ t) • rev (dZX x x y′) • rev (dZX t y′ t)) s)

-- (28)
e28 : ∀ (a c′ c : I) → Succ c′ c → suc (toℕ a) < toℕ c → parity (toℕ c ∸ toℕ a) ≡ false →
      (d ʷ) (zx {N} c a c) ≈ (d ʷ) (zx c′ c′ c • zx c′ a c′ • zx c c′ c)
e28 a c′ c s p q with odd-gap (toℕ a) (toℕ c′) (Eq.subst (λ t → suc (toℕ a) < t) s p)
... | k , xy′ , e₁ , e₂ , e₃ =
  trans (≡→≈ (Eq.trans (d-zx c a c (ne-ℕ (<⇒≢ (≤-trans (n≤1+n _) p))))
                       (Eq.cong (λ t → rev (dZX {m} t x t)) s)))
        (trans (D28 x y′ k xy′ e₁ e₂ (par-of e₃ (Eq.subst (λ t → parity (t ∸ x) ≡ false) s q)))
               (≡→≈ (Eq.sym rhs)))
  where
  x y′ : ℕ
  x  = toℕ a
  y′ = toℕ c′
  c′c : c′ ≢ c
  c′c = ne-ℕ (λ e → <⇒≢ (n<1+n y′) (Eq.trans e s))
  rhs : (d ʷ) (zx {N} c′ c′ c • zx c′ a c′ • zx c c′ c) ≡
        rev (dZX {m} y′ y′ (suc y′)) • rev (dZX y′ x y′) • rev (dZX (suc y′) y′ (suc y′))
  rhs = Eq.trans (Eq.cong₂ _•_ (d-zx c′ c′ c c′c) (Eq.cong₂ _•_ (d-zx c′ a c′ (ne-ℕ (<⇒≢ xy′))) (d-zx c c′ c c′c)))
                 (Eq.cong (λ t → rev (dZX {m} y′ y′ t) • rev (dZX y′ x y′) • rev (dZX t y′ t)) s)

-- (30)
e30 : ∀ (c a b : I) → a ≢ b → c ≢ a → c ≢ b → (d ʷ) (zx {N} c a b) ≈ (d ʷ) (zz c a • zx a a b)
e30 c a b ab ca cb = ≡→≈ (Eq.trans (d-zx c a b ab)
  (Eq.trans (Eq.cong rev (dZX-mid (toℕ c) (toℕ a) (toℕ b) (λ e → ca (toℕ-injective e)) (λ e → cb (toℕ-injective e))))
            (Eq.cong (rev (dZZ {m} (toℕ c) (toℕ a)) •_)
                     (Eq.sym (Eq.trans (d-zx a a b ab) (Eq.cong rev (dZX-self (λ e → ab (toℕ-injective e)))))))))

-- (33)
e33 : ∀ (b a : I) → (d ʷ) (zx {N} b a b) ≈ (d ʷ) (zx b b a)
e33 b a with a ≟F b
... | yes Eq.refl = refl
... | no ab = ≡→≈ (Eq.trans (d-zx b a b ab)
                    (Eq.trans (Eq.cong rev (sides (toℕ a) (toℕ b) (λ e → ab (toℕ-injective e))))
                              (Eq.sym (d-zx b b a (λ e → ab (Eq.sym e))))))
  where
  sides : ∀ x y → x ≢ y → dZX {m} y x y ≡ dZX y y x
  sides x y xy with <-cmp x y
  ... | tri< p _ _ = Eq.trans (dZX-hi p) (Eq.sym (dZX-hi′ p))
  ... | tri≈ _ e _ = ⊥-elim (xy e)
  ... | tri> _ _ p = Eq.trans (dZX-lo′ p) (Eq.sym (dZX-lo p))

-- (34)
e34 : ∀ (a b c e : I) → a ≢ b → c ≢ e → (d ʷ) (xx {N} a b c e) ≈ (d ʷ) (zx a a b • zx b c e)
e34 a b c e ab ce = ≡→≈ (Eq.trans (Eq.cong (d ʷ) (xx-letter a b c e ab ce))
                                  (Eq.sym (Eq.cong₂ _•_ (d-zx a a b ab) (d-zx b c e ce))))

------------------------------------------------------------------------
-- (35) and (42): the Hadamard pairs

hh-letter : ∀ (a b c e : I) (ab : a ≢ b) (ce : c ≢ e) → hh {N} a b c e ≡ [ HH a b c e ab ce ]ʷ
hh-letter a b c e ab ce with a ≟F b | c ≟F e
... | yes p | _     = ⊥-elim (ab p)
... | no _  | yes p = ⊥-elim (ce p)
... | no _  | no _  = Eq.refl

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true}  _ = Eq.refl
  ∧-l {false} ()

  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true}  e = e
  ∧-r {false} ()

  not-true : ∀ {b} → not b ≡ true → b ≡ false
  not-true {false} _ = Eq.refl
  not-true {true}  ()

  ᵇ-ne : ∀ {x y} → (x ≡ᵇ y) ≡ false → x ≢ y
  ᵇ-ne {x} e Eq.refl = t≢f (Eq.trans (Eq.sym (≡ᵇ-refl x)) e)
    where
    t≢f : true ≢ false
    t≢f ()

  dist-ab : ∀ x y z w → distinct4 x y z w ≡ true → x ≢ y
  dist-ab x y z w t = ᵇ-ne (not-true (∧-l t))

  dist-cd : ∀ x y z w → distinct4 x y z w ≡ true → z ≢ w
  dist-cd x y z w t = ᵇ-ne (not-true (∧-r (∧-r (∧-r (∧-r (∧-r t))))))

  dist4 : ∀ x y z w → x ≢ y → x ≢ z → x ≢ w → y ≢ z → y ≢ w → z ≢ w →
          not (x ≡ᵇ y) ∧ not (x ≡ᵇ z) ∧ not (x ≡ᵇ w) ∧ not (y ≡ᵇ z) ∧ not (y ≡ᵇ w) ∧ not (z ≡ᵇ w) ≡ true
  dist4 x y z w e₁ e₂ e₃ e₄ e₅ e₆
    rewrite ≡ᵇ-≢ x y e₁ | ≡ᵇ-≢ x z e₂ | ≡ᵇ-≢ x w e₃ | ≡ᵇ-≢ y z e₄ | ≡ᵇ-≢ y w e₅ | ≡ᵇ-≢ z w e₆ = Eq.refl

  dHH-true : ∀ x y z w → distinct4 x y z w ≡ true → dHH {m} x y z w ≡ dHH₄ x y z w
  dHH-true x y z w t = Eq.cong (λ β → if β then dHH₄ {m} x y z w else _) t

  dHH-false : ∀ x y z w → distinct4 x y z w ≡ false →
              dHH {m} x y z w ≡ dHH₄ (proj₁ (twoSmallest x y z w)) (proj₂ (twoSmallest x y z w)) z w •
                                dHH₄ x y (proj₁ (twoSmallest x y z w)) (proj₂ (twoSmallest x y z w))
  dHH-false x y z w f = Eq.cong (λ β → if β then dHH₄ {m} x y z w else _) f

  -- The Gray codes of 0, 1, 3, 2: no bit, bit 0, bit 1, both.
  hd-Z : ∀ k → hd (toBits k 0) ≡ false
  hd-Z zero    = Eq.refl
  hd-Z (suc k) = Eq.refl

  gray-Z : ∀ k → gray (toBits k 0) ≡ toBits k 0
  gray-Z zero    = Eq.refl
  gray-Z (suc k) = Eq.cong₂ _∷_ (hd-Z k) (gray-Z k)

  G₀ : Bits N
  G₀ = false ∷ false ∷ false ∷ toBits m 0

  g0 : gcode {m} 0 ≡ G₀
  g0 = Eq.cong₂ (λ h z → false ∷ false ∷ h ∷ z) (hd-Z m) (gray-Z m)

  g1 : gcode {m} 1 ≡ flipAt 0 G₀
  g1 = Eq.cong₂ (λ h z → true ∷ false ∷ h ∷ z) (hd-Z m) (gray-Z m)

  g3 : gcode {m} 3 ≡ flipAt 1 G₀
  g3 = Eq.cong₂ (λ h z → false ∷ true ∷ h ∷ z) (hd-Z m) (gray-Z m)

  g2 : gcode {m} 2 ≡ flipAt 0 (flipAt 1 G₀)
  g2 = Eq.cong₂ (λ h z → true ∷ true ∷ h ∷ z) (hd-Z m) (gray-Z m)

  cong-hpat : ∀ {a a′ b b′ c c′ e e′ : Bits N} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ →
              hpat a b c e ≡ hpat a′ b′ c′ e′
  cong-hpat Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  pat0132 : hpat (gcode {m} 0) (gcode 1) (gcode 3) (gcode 2) ≡ just (0 , 1)
  pat0132 = Eq.trans (cong-hpat g0 g1 g3 g2) (hpat-flips G₀ 0 1 (s≤s z≤n) (s≤s (s≤s z≤n)) (λ ()) Eq.refl Eq.refl)

  cong-hhℕ : ∀ {a a′ b b′ c c′ e e′ : ℕ} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → hhℕ {N} a b c e ≡ hhℕ a′ b′ c′ e′
  cong-hhℕ Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  cong-dHH : ∀ {a a′ b b′ c c′ e e′ : ℕ} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → dHH {m} a b c e ≡ dHH a′ b′ c′ e′
  cong-dHH Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

-- The standard pair decodes to the gadget of Definition 8.3.
d-hh0132 : (d ʷ) (hhℕ {N} 0 1 3 2) ≡ rev gadget
d-hh0132 = Eq.trans (Eq.cong (d ʷ) (Eq.trans (cong-hhℕ (Eq.sym toℕ-i₀) (Eq.sym toℕ-i₁) (Eq.sym toℕ-i₃) (Eq.sym toℕ-i₂))
                                            (Eq.trans (hhℕ-hh i₀ i₁ i₃ i₂) (hh-letter i₀ i₁ i₃ i₂ i₀≢i₁ i₃≢i₂))))
                    (Eq.cong rev (Eq.trans (cong-dHH toℕ-i₀ toℕ-i₁ toℕ-i₃ toℕ-i₂) (dHH₄-pat 0 1 3 2 0 1 pat0132)))
  where
  i₀≢i₁ : i₀ ≢ i₁
  i₀≢i₁ e = ᵇ-ne {0} {1} Eq.refl (Eq.trans (Eq.sym toℕ-i₀) (Eq.trans (Eq.cong toℕ e) toℕ-i₁))
  i₃≢i₂ : i₃ ≢ i₂
  i₃≢i₂ e = ᵇ-ne {3} {2} Eq.refl (Eq.trans (Eq.sym toℕ-i₃) (Eq.trans (Eq.cong toℕ e) toℕ-i₂))

private
  -- A word of signed exchanges decodes letter by letter.
  d-zx′ : ∀ (c a b : I) → (d ʷ) (zx {N} c a b) ≡ rev (dΣ {m} (zx c a b))
  d-zx′ c a b with a ≟F b
  ... | yes _ = Eq.refl
  ... | no _  = Eq.refl

  d-zxℕ : ∀ c a b → (d ʷ) (zxℕ {N} c a b) ≡ rev (dΣ {m} (zxℕ c a b))
  d-zxℕ c a b with toFin {N} c | toFin {N} a | toFin {N} b
  ... | nothing | _       | _       = Eq.refl
  ... | just _  | nothing | _       = Eq.refl
  ... | just _  | just _  | nothing = Eq.refl
  ... | just c′ | just a′ | just b′ = d-zx′ c′ a′ b′

  dΣ-• : ∀ {u v : Word (GenP N)} → (d ʷ) u ≡ rev (dΣ {m} u) → (d ʷ) v ≡ rev (dΣ {m} v) →
         (d ʷ) (u • v) ≡ rev (dΣ {m} (u • v))
  dΣ-• eu ev = Eq.cong₂ _•_ eu ev

  d-Σ : ∀ x y z w → (d ʷ) (Σ {N} x y z w) ≡ rev (dΣ {m} (Σ x y z w))
  d-Σ x y z w = dΣ-• (d-zxℕ _ _ _) (dΣ-• (d-zxℕ _ _ _) (dΣ-• (d-zxℕ _ _ _) (d-zxℕ _ _ _)))

  d-Σ′ : ∀ x y z w → (d ʷ) (Σ′ {N} x y z w) ≡ rev (dΣ {m} (Σ′ x y z w))
  d-Σ′ x y z w = dΣ-• (d-zxℕ _ _ _) (dΣ-• (d-zxℕ _ _ _) (dΣ-• (d-zxℕ _ _ _) (d-zxℕ _ _ _)))

-- (35)
e35 : ∀ (a b c e : I) → distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ e) ≡ true →
      hpat (code N a) (code N b) (code N c) (code N e) ≡ nothing →
      (d ʷ) (hh {N} a b c e) ≈
      (d ʷ) (Σ (toℕ a) (toℕ b) (toℕ c) (toℕ e) • hhℕ 0 1 3 2 • Σ′ (toℕ a) (toℕ b) (toℕ c) (toℕ e))
e35 a b c e dist np = begin
  (d ʷ) (hh a b c e)
    ≈⟨ ≡→≈ (Eq.cong (d ʷ) (hh-letter a b c e (ne-ℕ (dist-ab x y z w dist)) (ne-ℕ (dist-cd x y z w dist)))) ⟩
  rev (dHH x y z w)
    ≈⟨ ≡→≈ (Eq.cong rev (Eq.trans (dHH-true x y z w dist) (dHH₄-nopat x y z w np))) ⟩
  rev (dΣ (Σ′ x y z w) • gadget • dΣ (Σ x y z w))
    ≈⟨ rev3 (dΣ (Σ′ x y z w)) gadget (dΣ (Σ x y z w)) ⟩
  rev (dΣ (Σ x y z w)) • rev gadget • rev (dΣ (Σ′ x y z w))
    ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ (d-Σ x y z w) (Eq.cong₂ _•_ d-hh0132 (d-Σ′ x y z w)))) ⟩
  (d ʷ) (Σ x y z w • hhℕ 0 1 3 2 • Σ′ x y z w) ∎
  where
  x y z w : ℕ
  x = toℕ a
  y = toℕ b
  z = toℕ c
  w = toℕ e

private
  <8 : ∀ {k} → k < 8 → k < 2 ^ N
  <8 p = ≤-trans p (8≤2^ m)

-- (42)
e42 : ∀ (a b c e : I) → a ≢ b → c ≢ e → distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ e) ≡ false →
      (d ʷ) (hhℕ {N} (toℕ a) (toℕ b) (proj₁ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ e)))
                                   (proj₂ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ e))) •
             hhℕ (proj₁ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ e)))
                 (proj₂ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ e))) (toℕ c) (toℕ e))
        ≈ (d ʷ) (hh a b c e)
e42 a b c e ab ce nd = ≡→≈ (Eq.trans lhs (Eq.sym rhs))
  where
  module S = Small (small (toℕ a) (toℕ b) (toℕ c) (toℕ e))
  x y z w E F : ℕ
  x = toℕ a
  y = toℕ b
  z = toℕ c
  w = toℕ e
  E = S.e
  F = S.f
  E′ F′ : I
  E′ = fromℕ< (<8 S.e<8)
  F′ = fromℕ< (<8 S.f<8)
  vE : toℕ E′ ≡ E
  vE = toℕ-fromℕ< (<8 S.e<8)
  vF : toℕ F′ ≡ F
  vF = toℕ-fromℕ< (<8 S.f<8)
  ts₁ : proj₁ (twoSmallest x y z w) ≡ E
  ts₁ = Eq.cong proj₁ S.ts
  ts₂ : proj₂ (twoSmallest x y z w) ≡ F
  ts₂ = Eq.cong proj₂ S.ts
  EF : E ≢ F
  EF = <⇒≢ S.e<f
  E′F′ : E′ ≢ F′
  E′F′ q = EF (Eq.trans (Eq.sym vE) (Eq.trans (Eq.cong toℕ q) vF))
  sym≢ : ∀ {u v : ℕ} → u ≢ v → v ≢ u
  sym≢ ne q = ne (Eq.sym q)
  xy : x ≢ y
  xy q = ab (toℕ-injective q)
  zw : z ≢ w
  zw q = ce (toℕ-injective q)
  -- The two letters, indices decided.
  l₁ : hhℕ {N} x y (proj₁ (twoSmallest x y z w)) (proj₂ (twoSmallest x y z w)) ≡ hh a b E′ F′
  l₁ = Eq.trans (cong-hhℕ Eq.refl Eq.refl (Eq.trans ts₁ (Eq.sym vE)) (Eq.trans ts₂ (Eq.sym vF)))
                (hhℕ-hh a b E′ F′)
  l₂ : hhℕ {N} (proj₁ (twoSmallest x y z w)) (proj₂ (twoSmallest x y z w)) z w ≡ hh E′ F′ c e
  l₂ = Eq.trans (cong-hhℕ (Eq.trans ts₁ (Eq.sym vE)) (Eq.trans ts₂ (Eq.sym vF)) Eq.refl Eq.refl)
                (hhℕ-hh E′ F′ c e)
  lhs : (d ʷ) (hhℕ {N} x y (proj₁ (twoSmallest x y z w)) (proj₂ (twoSmallest x y z w)) •
               hhℕ (proj₁ (twoSmallest x y z w)) (proj₂ (twoSmallest x y z w)) z w)
        ≡ rev (dHH₄ {m} x y E F) • rev (dHH₄ E F z w)
  lhs = Eq.trans (Eq.cong₂ (λ u v → (d ʷ) (u • v)) (Eq.trans l₁ (hh-letter a b E′ F′ ab E′F′))
                                                  (Eq.trans l₂ (hh-letter E′ F′ c e E′F′ ce)))
                 (Eq.cong₂ _•_ (Eq.cong rev (Eq.trans (cong-dHH Eq.refl Eq.refl vE vF)
                                                      (dHH-true x y E F (dist4 x y E F xy (sym≢ S.ea) (sym≢ S.fa)
                                                                                       (sym≢ S.eb) (sym≢ S.fb) EF))))
                               (Eq.cong rev (Eq.trans (cong-dHH vE vF Eq.refl Eq.refl)
                                                      (dHH-true E F z w (dist4 E F z w EF S.ec S.ed S.fc S.fd zw)))))
  rhs : (d ʷ) (hh {N} a b c e) ≡ rev (dHH₄ {m} x y E F) • rev (dHH₄ E F z w)
  rhs = Eq.trans (Eq.cong (d ʷ) (hh-letter a b c e ab ce))
                 (Eq.cong rev (Eq.trans (dHH-false x y z w nd)
                                        (Eq.cong₂ (λ u v → dHH₄ {m} u v z w • dHH₄ x y u v) ts₁ ts₂)))
