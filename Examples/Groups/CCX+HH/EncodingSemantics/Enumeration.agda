------------------------------------------------------------------------
-- Presentations of groups
--
-- The enumeration-based encoder of `Encoding.agda` preserves the
-- semantics at every width: each gate acts as `gate-action` of
-- `Structural`, so every circuit's encoding has the ordinary circuit
-- matrix, and the two encoders give the same matrix.
--
-- `Encoding.agda` lists its letters by index: the exchange of a with
-- a + 2 ^ t, or the four-level block on a, a + 2 ^ p, a + 2 ^ q,
-- a + 2 ^ p + 2 ^ q, for every index a satisfying a bit condition.
-- `Structural` is defined by recursion on the width, a gate on wire 0
-- copied into the two contiguous halves and a shifted gate into the
-- two alternating halves.  The proof follows that recursion: one width
-- up, the enumeration over [0, 2 · 2 ^ m) splits into its two halves
-- (contiguous), or into the even and odd indices, which interleave
-- (alternating); the letters of each part are those one width down,
-- embedded (`EnumerationArith`).  Interleaved letters on the two sides
-- of a partition act as the two copies in parallel (`Blocks`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH.EncodingSemantics.Enumeration
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_)
open import Data.List.Base using (applyUpTo)
import Data.Nat.Base as ℕ
open import Data.Nat.Base using (ℕ ; zero ; suc ; s≤s ; z≤n)
  renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Encoding as En
import Examples.Groups.CCX+HH.StructuralEncoding as St
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; word)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (contiguous ; alternating)
open import Examples.Groups.CCX+HH.EncodingSemantics.EnumerationArith
open import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates using () renaming (bit to ⌊_⌋)
import Examples.Groups.CCX+HH-TwoLevel.Action as Action
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks
import Examples.Groups.CCX+HH.EncodingSemantics.Structural as Structural

open Action isCR adjI h
open Blocks isCR adjI h
open Structural isCR adjI h
  using (State ; x₀ ; cx₀ ; ccx₀ ; hh₀ ; gate-action ; gate-matrix ; interpret
        ; encoding-correct)

private
  variable
    n d N : ℕ

------------------------------------------------------------------------
-- Products of consecutive letters

-- f 0 • f 1 • … • f (k − 1).
Π : ℕ → (ℕ → Word (T.Gen N)) → Word (T.Gen N)
Π zero f = ε
Π (suc k) f = f 0 • Π k (λ i → f (suc i))

∏-Π : ∀ k (g : ℕ → ℕ) (f : ℕ → Word (T.Gen N)) →
  En.∏ (applyUpTo g k) f ≡ Π k (λ i → f (g i))
∏-Π zero g f = refl
∏-Π (suc k) g f = cong (f (g 0) •_) (∏-Π k (λ i → g (suc i)) f)

Π-cong : ∀ k {f f′ : ℕ → Word (T.Gen N)} → (∀ i → i ℕ.< k → f i ≡ f′ i) →
  Π k f ≡ Π k f′
Π-cong zero eq = refl
Π-cong (suc k) eq =
  cong₂ _•_ (eq 0 (s≤s z≤n)) (Π-cong k (λ i lt → eq (suc i) (s≤s lt)))

Π-word : ∀ k (e : Emb d N) (f : ℕ → Word (T.Gen d)) →
  Π k (λ i → word e (f i)) ≡ word e (Π k f)
Π-word zero e f = refl
Π-word (suc k) e f = cong (word e (f 0) •_) (Π-word k e (λ i → f (suc i)))

private
  act : ∀ {u w : Word (T.Gen N)} → u ≡ w → ∀ v → actVʷ u v ≡ actVʷ w v
  act eq v = cong (λ z → actVʷ z v) eq

Π-+ : ∀ m k (f : ℕ → Word (T.Gen N)) v →
  actVʷ (Π (m ℕ.+ k) f) v ≡ actVʷ (Π m f) (actVʷ (Π k (λ i → f (m ℕ.+ i))) v)
Π-+ zero k f v = refl
Π-+ (suc m) k f v = cong (actVʷ (f 0)) (Π-+ m k (λ i → f (suc i)) v)

-- The two halves of [0, 2 · 2 ^ m) are the contiguous halves.
Π-halves : ∀ m (f : ℕ → Word (T.Gen (2 ^ℕ m))) (g : ℕ → Word (T.Gen (2 ^ℕ suc m))) →
  (∀ i → i ℕ.< 2 ^ℕ m → g i ≡ word (left (contiguous (2 ^ℕ m))) (f i)) →
  (∀ i → i ℕ.< 2 ^ℕ m → g (2 ^ℕ m ℕ.+ i) ≡ word (right (contiguous (2 ^ℕ m))) (f i)) →
  ∀ v → actVʷ (Π (2 ^ℕ suc m) g) v ≡
    parallel (contiguous (2 ^ℕ m)) (actVʷ (Π (2 ^ℕ m) f)) (actVʷ (Π (2 ^ℕ m) f)) v
Π-halves m f g gl gr v = begin
  actVʷ (Π (2 ^ℕ suc m) g) v
    ≡⟨ Π-+ (2 ^ℕ m) (2 ^ℕ m ℕ.+ 0) g v ⟩
  actVʷ (Π (2 ^ℕ m) g) (actVʷ (Π (2 ^ℕ m ℕ.+ 0) g′) v)
    ≡⟨ cong (actVʷ (Π (2 ^ℕ m) g))
         (act (cong (λ c → Π c g′) (NP.+-identityʳ (2 ^ℕ m))) v) ⟩
  actVʷ (Π (2 ^ℕ m) g) (actVʷ (Π (2 ^ℕ m) g′) v)
    ≡⟨ cong₂ (λ u w → actVʷ u (actVʷ w v))
         (trans (Π-cong (2 ^ℕ m) gl) (Π-word (2 ^ℕ m) (left C) f))
         (trans (Π-cong (2 ^ℕ m) gr) (Π-word (2 ^ℕ m) (right C) f)) ⟩
  actVʷ (encode-parallel C (Π (2 ^ℕ m) f) (Π (2 ^ℕ m) f)) v
    ≡⟨ encode-parallel-correct C (Π (2 ^ℕ m) f) (Π (2 ^ℕ m) f) v ⟩
  parallel C (actVʷ (Π (2 ^ℕ m) f)) (actVʷ (Π (2 ^ℕ m) f)) v ∎
  where
  open ≡-Reasoning
  C = contiguous (2 ^ℕ m)
  g′ = λ i → g (2 ^ℕ m ℕ.+ i)

-- Letters alternating between the two sides of a partition act as the
-- two products in parallel.
Π-interleave : (p : Partition d N) (k : ℕ) (f : ℕ → Word (T.Gen d))
  (g : ℕ → Word (T.Gen N)) →
  (∀ i → i ℕ.< k → g (i ℕ.* 2) ≡ word (left p) (f i)) →
  (∀ i → i ℕ.< k → g (suc (i ℕ.* 2)) ≡ word (right p) (f i)) →
  ∀ v → actVʷ (Π (k ℕ.* 2) g) v ≡ parallel p (actVʷ (Π k f)) (actVʷ (Π k f)) v
Π-interleave p zero f g gl gr v = sym (parallel-id p v)
Π-interleave p (suc k) f g gl gr v = begin
  actVʷ (g 0) (actVʷ (g 1) (actVʷ (Π (k ℕ.* 2) g″) v))
    ≡⟨ cong₂ (λ u w → actVʷ u (actVʷ w (actVʷ (Π (k ℕ.* 2) g″) v)))
         (gl 0 (s≤s z≤n)) (gr 0 (s≤s z≤n)) ⟩
  actVʷ (encode-parallel p (f 0) (f 0)) (actVʷ (Π (k ℕ.* 2) g″) v)
    ≡⟨ encode-parallel-correct p (f 0) (f 0) _ ⟩
  parallel p (actVʷ (f 0)) (actVʷ (f 0)) (actVʷ (Π (k ℕ.* 2) g″) v)
    ≡⟨ cong (parallel p (actVʷ (f 0)) (actVʷ (f 0)))
         (Π-interleave p k f′ g″ (λ i lt → gl (suc i) (s≤s lt))
           (λ i lt → gr (suc i) (s≤s lt)) v) ⟩
  parallel p (actVʷ (f 0)) (actVʷ (f 0))
    (parallel p (actVʷ (Π k f′)) (actVʷ (Π k f′)) v)
    ≡⟨ parallel-compose p (actVʷ (f 0)) (actVʷ (f 0)) (actVʷ (Π k f′)) (actVʷ (Π k f′)) v ⟩
  parallel p (actVʷ (Π (suc k) f)) (actVʷ (Π (suc k) f)) v ∎
  where
  open ≡-Reasoning
  f′ = λ i → f (suc i)
  g″ = λ i → g (suc (suc i))

------------------------------------------------------------------------
-- The encoder's products

private
  X-cond : ℕ → ℕ → Bool
  X-cond t a = not (En.bit a t)

  CX-cond : ℕ → ℕ → ℕ → Bool
  CX-cond c t a = En.bit a c ∧ not (En.bit a t)

  CCX-cond : ℕ → ℕ → ℕ → ℕ → Bool
  CCX-cond c d t a = En.bit a c ∧ En.bit a d ∧ not (En.bit a t)

  E-X : ∀ n t → En.E-X n t ≡ Π (2 ^ℕ n) (bodyX n t (X-cond t))
  E-X n t = ∏-Π (2 ^ℕ n) (λ i → i) _

  E-CX : ∀ n c t → En.E-CX n c t ≡ Π (2 ^ℕ n) (bodyX n t (CX-cond c t))
  E-CX n c t = ∏-Π (2 ^ℕ n) (λ i → i) _

  E-CCX : ∀ n c d t → En.E-CCX n c d t ≡ Π (2 ^ℕ n) (bodyX n t (CCX-cond c d t))
  E-CCX n c d t = ∏-Π (2 ^ℕ n) (λ i → i) _

  E-HH : ∀ n p q → En.E-HH n p q ≡ Π (2 ^ℕ n) (bodyK n p q)
  E-HH n p q = ∏-Π (2 ^ℕ n) (λ i → i) _

------------------------------------------------------------------------
-- One wire up at the bottom

private
  bottom-X : ∀ m t (cond cond′ : ℕ → Bool) →
    (∀ a β → cond′ (2 ℕ.* a ℕ.+ ⌊ β ⌋) ≡ cond a) → ∀ v →
    actVʷ (Π (2 ^ℕ suc m) (bodyX (suc m) (suc t) cond′)) v ≡
    parallel (alternating (2 ^ℕ m))
      (actVʷ (Π (2 ^ℕ m) (bodyX m t cond))) (actVʷ (Π (2 ^ℕ m) (bodyX m t cond))) v
  bottom-X m t cond cond′ ok v = trans
    (act (cong (λ c → Π c (bodyX (suc m) (suc t) cond′)) (NP.*-comm 2 (2 ^ℕ m))) v)
    (Π-interleave (alternating (2 ^ℕ m)) (2 ^ℕ m) (bodyX m t cond)
      (bodyX (suc m) (suc t) cond′)
      (λ i _ → trans (cong (bodyX (suc m) (suc t) cond′) (even-index i))
        (bodyX-alt m t false cond cond′ (λ a → ok a false) i))
      (λ i _ → trans (cong (bodyX (suc m) (suc t) cond′) (odd-index i))
        (bodyX-alt m t true cond cond′ (λ a → ok a true) i))
      v)

  bottom-K : ∀ m p v →
    actVʷ (Π (2 ^ℕ suc m) (bodyK (suc m) (suc p) (suc (suc p)))) v ≡
    parallel (alternating (2 ^ℕ m))
      (actVʷ (Π (2 ^ℕ m) (bodyK m p (suc p))))
      (actVʷ (Π (2 ^ℕ m) (bodyK m p (suc p)))) v
  bottom-K m p v = trans
    (act (cong (λ c → Π c (bodyK (suc m) (suc p) (suc (suc p)))) (NP.*-comm 2 (2 ^ℕ m))) v)
    (Π-interleave (alternating (2 ^ℕ m)) (2 ^ℕ m) (bodyK m p (suc p))
      (bodyK (suc m) (suc p) (suc (suc p)))
      (λ i _ → trans (cong (bodyK (suc m) (suc p) (suc (suc p))) (even-index i))
        (bodyK-alt m p false i))
      (λ i _ → trans (cong (bodyK (suc m) (suc p) (suc (suc p))) (odd-index i))
        (bodyK-alt m p true i))
      v)

-- A shifted gate's encoding is its encoding one wire down, copied into
-- the two alternating halves.
shift : ∀ n w v →
  actVʷ (En.encode-view (suc n) (En.up w)) v ≡
  parallel (alternating (2 ^ℕ n))
    (actVʷ (En.encode-view n w)) (actVʷ (En.encode-view n w)) v
shift n (En.at-X t) v = trans (act (E-X (suc n) (suc t)) v)
  (trans (bottom-X n t (X-cond t) (X-cond (suc t))
           (λ a β → cong not (bit-high a β t)) v)
    (sym (parallel-cong (alternating (2 ^ℕ n)) (act (E-X n t)) (act (E-X n t)) v)))
shift n (En.at-CX t) v = trans (act (E-CX (suc n) (suc (suc t)) (suc t)) v)
  (trans (bottom-X n t (CX-cond (suc t) t) (CX-cond (suc (suc t)) (suc t))
           (λ a β → cong₂ _∧_ (bit-high a β (suc t)) (cong not (bit-high a β t))) v)
    (sym (parallel-cong (alternating (2 ^ℕ n))
      (act (E-CX n (suc t) t)) (act (E-CX n (suc t) t)) v)))
shift n (En.at-CCX t) v = trans (act (E-CCX (suc n) (suc (suc t)) (suc (suc (suc t))) (suc t)) v)
  (trans (bottom-X n t (CCX-cond (suc t) (suc (suc t)) t)
            (CCX-cond (suc (suc t)) (suc (suc (suc t))) (suc t))
           (λ a β → cong₂ _∧_ (bit-high a β (suc t))
             (cong₂ _∧_ (bit-high a β (suc (suc t))) (cong not (bit-high a β t)))) v)
    (sym (parallel-cong (alternating (2 ^ℕ n))
      (act (E-CCX n (suc t) (suc (suc t)) t)) (act (E-CCX n (suc t) (suc (suc t)) t)) v)))
shift n (En.at-HH t) v = trans (act (E-HH (suc n) (suc t) (suc (suc t))) v)
  (trans (bottom-K n t v)
    (sym (parallel-cong (alternating (2 ^ℕ n))
      (act (E-HH n t (suc t))) (act (E-HH n t (suc t))) v)))

------------------------------------------------------------------------
-- One wire up at the top, and the four gates on wire 0

private
  not-true : ∀ {b} → not b ≡ true → b ≡ false
  not-true {false} _ = refl

  ∧-not : ∀ {b c} → b ∧ not c ≡ true → c ≡ false
  ∧-not {true} p = not-true p

  top-X : ∀ m (cond : ℕ → Bool) → 0 ℕ.< m →
    (∀ a → cond a ≡ true → En.bit a 0 ≡ false) →
    (∀ a → cond (2 ^ℕ m ℕ.+ a) ≡ cond a) → ∀ v →
    actVʷ (Π (2 ^ℕ suc m) (bodyX (suc m) 0 cond)) v ≡
    parallel (contiguous (2 ^ℕ m))
      (actVʷ (Π (2 ^ℕ m) (bodyX m 0 cond))) (actVʷ (Π (2 ^ℕ m) (bodyX m 0 cond))) v
  top-X m cond m>0 clear top = Π-halves m (bodyX m 0 cond) (bodyX (suc m) 0 cond)
    (bodyX-left m m>0 cond clear top) (bodyX-right m m>0 cond clear top)

  opaque
    unfolding actV set₁ set₂

    X-base : ∀ v → actVʷ (En.E-X 1 0) v ≡ x₀ v
    X-base (a ∷ b ∷ []) = refl

    CX-base : ∀ v → actVʷ (En.E-CX 2 1 0) v ≡ cx₀ v
    CX-base (a ∷ b ∷ c ∷ d ∷ []) = refl

    HH-base : ∀ v → actVʷ (En.E-HH 2 0 1) v ≡ hh₀ v
    HH-base (a ∷ b ∷ c ∷ d ∷ []) = refl

    CCX-base : ∀ v → actVʷ (En.E-CCX 3 1 2 0) v ≡ ccx₀ v
    CCX-base (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ j ∷ []) = refl

  -- From one width to the next, through Π-halves.
  step : ∀ m (E : ℕ → Word (T.Gen (2 ^ℕ m))) (E′ : ℕ → Word (T.Gen (2 ^ℕ suc m)))
    (W : Word (T.Gen (2 ^ℕ m))) (W′ : Word (T.Gen (2 ^ℕ suc m)))
    (F : State m → State m) →
    W ≡ Π (2 ^ℕ m) E → W′ ≡ Π (2 ^ℕ suc m) E′ →
    (∀ v → actVʷ (Π (2 ^ℕ suc m) E′) v ≡
       parallel (contiguous (2 ^ℕ m)) (actVʷ (Π (2 ^ℕ m) E)) (actVʷ (Π (2 ^ℕ m) E)) v) →
    (∀ v → actVʷ W v ≡ F v) →
    ∀ v → actVʷ W′ v ≡ parallel (contiguous (2 ^ℕ m)) F F v
  step m E E′ W W′ F eq eq′ halves ih v = trans (act eq′ v)
    (trans (halves v)
      (parallel-cong (contiguous (2 ^ℕ m))
        (λ u → trans (act (sym eq) u) (ih u)) (λ u → trans (act (sym eq) u) (ih u)) v))

X-correct : ∀ n v → actVʷ (En.E-X (suc n) 0) v ≡ gate-action (gate₁ {n} X-gate) v
X-correct zero = X-base
X-correct (suc n) = step (suc n) _ _ _ _ _ (E-X (suc n) 0) (E-X (suc (suc n)) 0)
  (top-X (suc n) (X-cond 0) (s≤s z≤n) (λ a → not-true)
    (λ a → cong not (bit-top (suc n) a 0 (s≤s z≤n))))
  (X-correct n)

CX-correct : ∀ n v → actVʷ (En.E-CX (suc (suc n)) 1 0) v ≡ gate-action (gate₂ {n} CX-gate) v
CX-correct zero = CX-base
CX-correct (suc n) = step (suc (suc n)) _ _ _ _ _
  (E-CX (suc (suc n)) 1 0) (E-CX (suc (suc (suc n))) 1 0)
  (top-X (suc (suc n)) (CX-cond 1 0) (s≤s z≤n) (λ a → ∧-not)
    (λ a → cong₂ _∧_ (bit-top (suc (suc n)) a 1 (s≤s (s≤s z≤n)))
      (cong not (bit-top (suc (suc n)) a 0 (s≤s z≤n)))))
  (CX-correct n)

CCX-correct : ∀ n v →
  actVʷ (En.E-CCX (suc (suc (suc n))) 1 2 0) v ≡ gate-action (gate₃ {n} CCX-gate) v
CCX-correct zero = CCX-base
CCX-correct (suc n) = step (suc (suc (suc n))) _ _ _ _ _
  (E-CCX (suc (suc (suc n))) 1 2 0) (E-CCX (suc (suc (suc (suc n)))) 1 2 0)
  (top-X (suc (suc (suc n))) (CCX-cond 1 2 0) (s≤s z≤n)
    (λ a p → ∧-not {En.bit a 2} (∧-right′ {En.bit a 1} {En.bit a 2 ∧ not (En.bit a 0)} p))
    (λ a → cong₂ _∧_ (bit-top m′ a 1 (s≤s (s≤s z≤n)))
      (cong₂ _∧_ (bit-top m′ a 2 (s≤s (s≤s (s≤s z≤n))))
        (cong not (bit-top m′ a 0 (s≤s z≤n))))))
  (CCX-correct n)
  where
  m′ = suc (suc (suc n))
  ∧-right′ : ∀ {b c} → b ∧ c ≡ true → c ≡ true
  ∧-right′ {true} p = p

HH-correct : ∀ n v → actVʷ (En.E-HH (suc (suc n)) 0 1) v ≡ gate-action (gate₂ {n} HH-gate) v
HH-correct zero = HH-base
HH-correct (suc n) = step (suc (suc n)) _ _ _ _ _
  (E-HH (suc (suc n)) 0 1) (E-HH (suc (suc (suc n))) 0 1)
  (Π-halves (suc (suc n)) (bodyK (suc (suc n)) 0 1) (bodyK (suc (suc (suc n))) 0 1)
    (bodyK-left (suc (suc n)) (s≤s (s≤s z≤n)))
    (bodyK-right (suc (suc n)) (s≤s (s≤s z≤n))))
  (HH-correct n)

------------------------------------------------------------------------
-- Every gate, every circuit

enumeration-action : (g : Gen n) → ∀ v → actVʷ (En.e g) v ≡ gate-action g v
enumeration-action (gate₀ ())
enumeration-action (gate₁ {n} X-gate) = X-correct n
enumeration-action (gate₂ {n} CX-gate) = CX-correct n
enumeration-action (gate₂ {n} HH-gate) = HH-correct n
enumeration-action (gate₃ {n} CCX-gate) = CCX-correct n
enumeration-action (_↥ {n} g) v = trans (shift n (En.view g) v)
  (parallel-cong (alternating (2 ^ℕ n))
    (enumeration-action g) (enumeration-action g) v)

enumeration-correct-gate : (g : Gen n) → ⟦ En.e g ⟧ᵐ ≡ gate-matrix g
enumeration-correct-gate g = col-ext λ j →
  trans (col-actMʷ (En.e g) 𝕀 j)
    (trans (enumeration-action g (col 𝕀 j))
      (sym (!-tabulate (λ k → gate-action g (col 𝕀 k)) j)))

-- The enumeration-based encoding has the ordinary circuit matrix.
enumeration-correct : (w : Circuit n) → ⟦ En.encode w ⟧ᵐ ≡ interpret w
enumeration-correct [ g ]ʷ = enumeration-correct-gate g
enumeration-correct ε = refl
enumeration-correct (u • v) = trans (⟦•⟧ᵐ (En.encode u) (En.encode v))
  (cong₂ _·*·_ (enumeration-correct u) (enumeration-correct v))

-- The two encoders agree.
encoders-agree : (w : Circuit n) → ⟦ En.encode w ⟧ᵐ ≡ ⟦ St.encode w ⟧ᵐ
encoders-agree w = trans (enumeration-correct w) (sym (encoding-correct w))
