------------------------------------------------------------------------
-- Presentations of groups
--
-- The X gates of the hidden shift circuit: their path variables and
-- their phase
--
-- In figure 3(a) of Amy's "Towards Large-scale Functional Verification
-- of Universal Quantum Circuits" (QPL 2018) the shift is applied by X
-- gates, X^s on each side of the oracle O_f.  X is not a gate of
-- definition 2.9's set; here it is H R₁ H (PathSum.HiddenShift.Layers),
-- so the layer X^s has two Hadamards, and two path variables, for each
-- wire w with s_w = 1 (norm (flips s) of them in all).
-- PathSum.HiddenShift.Runs reads the layer along a path: the X on wire
-- w reads the bits at positions xrev s w true (its first Hadamard) and
-- xrev s w false (its second), counted from the end of the layer, and
-- adds ½ times xβ to the phase.
--
-- This module is about those positions and that parity.  The positions
-- of the wires with s_w = 1 are below norm (flips s) (xrev<), distinct
-- (xrev-inj), and every position is one of them (xexists), so a
-- position of the layer names a wire and a Hadamard (xdecF, xposF,
-- inverse to each other: xdec-xpos, xdec-rev) -- the labelling the
-- reduction of figure 3(a) needs (PathSum.HiddenShift.ExistsCircuit).
-- And xβ, the parity of the layer, reads only the wires with s_w = 1
-- (xβ-cong), vanishes when every first Hadamard's bit is 0 (xβ-zero),
-- and changes, when the first bit of the X on wire w flips, by
-- v_w ⊕ 1 ⊕ c₂ (xβ-∂), c₂ being the second bit: the derivative [HH]
-- asks for, removing the X's two variables and leaving v_w ⊕ 1 on the
-- wire, which is X.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.XLayer (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ; xor-same)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Nat.Base using (zero; suc; _<_; _≤_; s≤s; z≤n; s≤s⁻¹)
  renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Gates M₀ using (lift; norm-lift)
open import PathSum.HiddenShift.Layers M₀ using (flipʰ; flips)
open import PathSum.HiddenShift.Runs M₀ using (nF; xrev; xβʰ; xβ; xout)
open import PathSum.HiddenShift.Walsh using (xor-medial)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using (norm)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The positions

-- The layer on a wire more: two more Hadamards if s₀ = 1.

nF-cons : (s : Assign (suc n)) →
          nF s ≡ (if s zero then 2 else 0) ℕ+ nF (λ i → s (suc i))
nF-cons s = go (s zero)
  where
  go : ∀ b → norm (flipʰ b (lift (flips (λ i → s (suc i))))) ≡
             (if b then 2 else 0) ℕ+ nF (λ i → s (suc i))
  go false = norm-lift (flips (λ i → s (suc i)))
  go true  = cong (λ k → suc (suc k)) (norm-lift (flips (λ i → s (suc i))))

-- The X on a wire with s_w = 1 reads positions of the layer.

xrev< : (s : Assign n) (w : Fin n) (t : Bool) → s w ≡ true →
        xrev s w t < nF s
xrev< {suc n} s zero t h =
  subst (xrev s zero t <_) (sym (nF-cons s)) (lt (s zero) h t)
  where
  R : ℕ
  R = nF (λ i → s (suc i))

  lt : ∀ b → b ≡ true → ∀ t → xrev s zero t < (if b then 2 else 0) ℕ+ R
  lt true refl true  = ℕ.n<1+n (suc R)
  lt true refl false = ℕ.m<n+m R (s≤s z≤n)
  lt false ()
xrev< {suc n} s (suc w) t h = subst (xrev s (suc w) t <_) (sym (nF-cons s))
  (ℕ.<-≤-trans (xrev< (λ i → s (suc i)) w t h)
               (ℕ.m≤n+m (nF (λ i → s (suc i))) (if s zero then 2 else 0)))

-- Different Hadamards read different positions.

private
  -- Both of wire 0's positions come after the rest's.

  xrev-0≥ : (s : Assign (suc n)) (t : Bool) →
            nF (λ i → s (suc i)) ≤ xrev s zero t
  xrev-0≥ s true  = ℕ.n≤1+n _
  xrev-0≥ s false = ℕ.≤-refl

  zero-suc : (s : Assign (suc n)) (w : Fin n) (t t′ : Bool) → s (suc w) ≡ true →
             xrev s zero t ≢ xrev s (suc w) t′
  zero-suc s w t t′ h e = ℕ.<⇒≱ (xrev< (λ i → s (suc i)) w t′ h)
    (subst (nF (λ i → s (suc i)) ≤_) e (xrev-0≥ s t))

xrev-inj : (s : Assign n) (w w′ : Fin n) (t t′ : Bool) →
           s w ≡ true → s w′ ≡ true → xrev s w t ≡ xrev s w′ t′ →
           (w ≡ w′) × (t ≡ t′)
xrev-inj {suc n} s zero zero t t′ h h′ e = refl , bits t t′ e
  where
  bits : ∀ t t′ → xrev s zero t ≡ xrev s zero t′ → t ≡ t′
  bits true  true  _ = refl
  bits false false _ = refl
  bits true  false e = ⊥-elim (ℕ.1+n≢n e)
  bits false true  e = ⊥-elim (ℕ.1+n≢n (sym e))
xrev-inj {suc n} s zero (suc w′) t t′ h h′ e = ⊥-elim (zero-suc s w′ t t′ h′ e)
xrev-inj {suc n} s (suc w) zero t t′ h h′ e =
  ⊥-elim (zero-suc s w t′ t h (sym e))
xrev-inj {suc n} s (suc w) (suc w′) t t′ h h′ e =
  let (w≡w′ , t≡t′) = xrev-inj (λ i → s (suc i)) w w′ t t′ h h′ e
  in cong suc w≡w′ , t≡t′

-- Every position of the layer is read by one of them.

xexists : (s : Assign n) (p : ℕ) → p < nF s →
          Σ (Fin n × Bool) (λ wt → (s (proj₁ wt) ≡ true) ×
                                   (xrev s (proj₁ wt) (proj₂ wt) ≡ p))
xexists {zero}  s p ()
xexists {suc n} s p lt = go (s zero) refl (subst (p <_) (nF-cons s) lt)
  where
  s′ : Assign n
  s′ i = s (suc i)

  R : ℕ
  R = nF s′

  onward : p < R → Σ (Fin (suc n) × Bool) (λ wt → (s (proj₁ wt) ≡ true) ×
                                           (xrev s (proj₁ wt) (proj₂ wt) ≡ p))
  onward p<R with xexists s′ p p<R
  ... | (w , t) , h , eq = (suc w , t) , h , eq

  go : ∀ b → s zero ≡ b → p < (if b then 2 else 0) ℕ+ R →
       Σ (Fin (suc n) × Bool) (λ wt → (s (proj₁ wt) ≡ true) ×
                                     (xrev s (proj₁ wt) (proj₂ wt) ≡ p))
  go false e lt′ = onward lt′
  go true  e lt′ with ℕ.<-cmp p R
  ... | tri< p<R _   _   = onward p<R
  ... | tri≈ _   p≡R _   = (zero , false) , e , sym p≡R
  ... | tri> _   _   R<p =
    (zero , true) , e , sym (ℕ.≤-antisym (s≤s⁻¹ lt′) R<p)

-- A position, named by its wire and Hadamard, and back.

xposF : (s : Assign n) (w : Fin n) (t : Bool) → s w ≡ true → Fin (nF s)
xposF s w t h = fromℕ< (xrev< s w t h)

xdecF : (s : Assign n) → Fin (nF s) → Fin n × Bool
xdecF s q = proj₁ (xexists s (toℕ q) (Fin.toℕ<n q))

xdec-ok : (s : Assign n) (q : Fin (nF s)) → s (proj₁ (xdecF s q)) ≡ true
xdec-ok s q = proj₁ (proj₂ (xexists s (toℕ q) (Fin.toℕ<n q)))

xdec-rev : (s : Assign n) (q : Fin (nF s)) →
           xrev s (proj₁ (xdecF s q)) (proj₂ (xdecF s q)) ≡ toℕ q
xdec-rev s q = proj₂ (proj₂ (xexists s (toℕ q) (Fin.toℕ<n q)))

xdec-xpos : (s : Assign n) (w : Fin n) (t : Bool) (h : s w ≡ true) →
            xdecF s (xposF s w t h) ≡ (w , t)
xdec-xpos s w t h =
  let (e₁ , e₂) = xrev-inj s _ w _ t (xdec-ok s (xposF s w t h)) h
                    (trans (xdec-rev s (xposF s w t h))
                           (Fin.toℕ-fromℕ< (xrev< s w t h)))
  in cong₂ _,_ e₁ e₂


------------------------------------------------------------------------
-- The parity

private
  xor-cancel-front : ∀ x p q → (x xor p) xor (x xor q) ≡ p xor q
  xor-cancel-front x p q =
    trans (xor-medial x p x q) (cong (_xor (p xor q)) (xor-same x))

-- One gate's term, then the rest's.

xβʰ-cong : ∀ b {a a′ c₁ c₁′ c₂ c₂′ r r′ : Bool} →
           (b ≡ true → a ≡ a′) → (b ≡ true → c₁ ≡ c₁′) →
           (b ≡ true → c₂ ≡ c₂′) → r ≡ r′ →
           xβʰ b a c₁ c₂ r ≡ xβʰ b a′ c₁′ c₂′ r′
xβʰ-cong false ha h₁ h₂ hr = hr
xβʰ-cong true  ha h₁ h₂ hr =
  cong₂ _xor_ (cong₂ _∧_ (ha refl) (h₁ refl))
    (cong₂ _xor_ (h₁ refl) (cong₂ _xor_ (cong₂ _∧_ (h₁ refl) (h₂ refl)) hr))

xβʰ-rest : ∀ b a c₁ c₂ r r′ →
           xβʰ b a c₁ c₂ r xor xβʰ b a c₁ c₂ r′ ≡ r xor r′
xβʰ-rest false a c₁ c₂ r r′ = refl
xβʰ-rest true  a c₁ c₂ r r′ =
  trans (xor-cancel-front (a ∧ c₁) _ _)
    (trans (xor-cancel-front c₁ _ _) (xor-cancel-front (c₁ ∧ c₂) r r′))

-- xβ reads the wires with s_w = 1 only.

xβ-cong : (s : Assign n) {v v′ b₁ b₁′ b₂ b₂′ : Assign n} →
          (∀ w → s w ≡ true → v w ≡ v′ w) →
          (∀ w → s w ≡ true → b₁ w ≡ b₁′ w) →
          (∀ w → s w ≡ true → b₂ w ≡ b₂′ w) →
          xβ s v b₁ b₂ ≡ xβ s v′ b₁′ b₂′
xβ-cong {zero}  s hv h₁ h₂ = refl
xβ-cong {suc n} s hv h₁ h₂ =
  xβʰ-cong (s zero) (hv zero) (h₁ zero) (h₂ zero)
    (xβ-cong (λ i → s (suc i)) (λ w → hv (suc w)) (λ w → h₁ (suc w))
             (λ w → h₂ (suc w)))

-- With every first bit 0 it vanishes.

xβ-zero : (s : Assign n) {v b₁ b₂ : Assign n} →
          (∀ w → s w ≡ true → b₁ w ≡ false) → xβ s v b₁ b₂ ≡ false
xβ-zero {zero}  s h = refl
xβ-zero {suc n} s {v} {b₁} {b₂} h =
  head (s zero) (v zero) (b₁ zero) (b₂ zero) _ (h zero)
       (xβ-zero (λ i → s (suc i)) (λ w → h (suc w)))
  where
  head : ∀ b a c₁ c₂ r → (b ≡ true → c₁ ≡ false) → r ≡ false →
         xβʰ b a c₁ c₂ r ≡ false
  head false a c₁ c₂ r hc hr = hr
  head true  a c₁ c₂ r hc hr = trans
    (cong₂ (λ c r → (a ∧ c) xor (c xor ((c ∧ c₂) xor r))) (hc refl) hr)
    (cong (_xor false) (∧-zeroʳ a))

-- Its derivative in the first bit of the X on wire w.

xβ-∂ : (s : Assign n) (w : Fin n) → s w ≡ true →
       {v v′ b₁ b₁′ b₂ b₂′ : Assign n} →
       (∀ w′ → s w′ ≡ true → v w′ ≡ v′ w′) →
       (∀ w′ → s w′ ≡ true → w′ ≢ w → b₁ w′ ≡ b₁′ w′) →
       (∀ w′ → s w′ ≡ true → b₂ w′ ≡ b₂′ w′) →
       b₁ w ≡ true → b₁′ w ≡ false →
       xβ s v b₁ b₂ xor xβ s v′ b₁′ b₂′ ≡ (v′ w xor true) xor b₂′ w
xβ-∂ {suc n} s zero h {v} {v′} {b₁} {b₁′} {b₂} {b₂′} hv h₁ h₂ t f = trans
  (cong₂ _xor_
    (xβʰ-cong (s zero) (hv zero) (λ _ → t) (h₂ zero) rest)
    (xβʰ-cong (s zero) (λ _ → refl) (λ _ → f) (λ _ → refl) refl))
  (flip (s zero) h (v′ zero) (b₂′ zero)
        (xβ (λ i → s (suc i)) (λ i → v′ (suc i)) (λ i → b₁′ (suc i))
            (λ i → b₂′ (suc i))))
  where
  rest : xβ (λ i → s (suc i)) (λ i → v (suc i)) (λ i → b₁ (suc i))
            (λ i → b₂ (suc i)) ≡
         xβ (λ i → s (suc i)) (λ i → v′ (suc i)) (λ i → b₁′ (suc i))
            (λ i → b₂′ (suc i))
  rest = xβ-cong (λ i → s (suc i)) (λ w → hv (suc w))
                 (λ w e → h₁ (suc w) e (λ ())) (λ w → h₂ (suc w))

  flip : ∀ b → b ≡ true → ∀ a c₂ r →
         xβʰ b a true c₂ r xor xβʰ b a false c₂ r ≡ (a xor true) xor c₂
  flip true refl false false false = refl
  flip true refl false false true  = refl
  flip true refl false true  false = refl
  flip true refl false true  true  = refl
  flip true refl true  false false = refl
  flip true refl true  false true  = refl
  flip true refl true  true  false = refl
  flip true refl true  true  true  = refl
  flip false ()
xβ-∂ {suc n} s (suc w) h {v} {v′} {b₁} {b₁′} {b₂} {b₂′} hv h₁ h₂ t f = trans
  (cong (xβʰ (s zero) (v zero) (b₁ zero) (b₂ zero) r xor_)
        (sym (xβʰ-cong (s zero) (hv zero) (λ e → h₁ zero e (λ ()))
                       (h₂ zero) refl)))
  (trans (xβʰ-rest (s zero) (v zero) (b₁ zero) (b₂ zero) r r′)
         (xβ-∂ (λ i → s (suc i)) w h (λ w′ → hv (suc w′))
               (λ w′ e ne → h₁ (suc w′) e (λ eq → ne (Fin.suc-injective eq)))
               (λ w′ → h₂ (suc w′)) t f))
  where
  r r′ : Bool
  r  = xβ (λ i → s (suc i)) (λ i → v (suc i)) (λ i → b₁ (suc i))
          (λ i → b₂ (suc i))
  r′ = xβ (λ i → s (suc i)) (λ i → v′ (suc i)) (λ i → b₁′ (suc i))
          (λ i → b₂′ (suc i))

-- What X^s leaves on the wires reads v everywhere, and the second bits
-- where s_w = 1.

xout-cong : (s : Assign n) {v v′ b₂ b₂′ : Assign n} →
            (∀ w → v w ≡ v′ w) → (∀ w → s w ≡ true → b₂ w ≡ b₂′ w) →
            ∀ w → xout s v b₂ w ≡ xout s v′ b₂′ w
xout-cong s {v} {v′} {b₂} {b₂′} hv h₂ w = pick (s w) refl
  where
  pick : ∀ b → s w ≡ b →
         (if b then b₂ w else v w) ≡ (if b then b₂′ w else v′ w)
  pick true  e = h₂ w e
  pick false e = hv w
