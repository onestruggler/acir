------------------------------------------------------------------------
-- Presentations of groups
--
-- The swaps of a gate keep its window in order.
--
-- Transport.placed writes a gate as ⌈ inv N ⌉ • top x₄ • ⌈ N ⌉.  Read
-- backwards, N⁻¹ sends the window state of h, under any colouring t of
-- the controls, to a state whose index increases with h (`mono-placed`):
-- a swap word one wire up keeps the order below it (the interleaved
-- partition is an increasing embedding), and the cycle that moves the
-- bottom wire to the top appends a bit above (`cycA-inv-act`, and the
-- contiguous partition, BinaryBasis.idx-append).  So the sixteen states
-- of a window gate's frame, listed by h, have increasing indices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.GateMono where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _^_)
open import Data.Product.Base using (proj₁)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι ; mono)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (select)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis
  using (cons ; append ; idx ; bits ; idx-cong ; idx-bits ; idx-append)
open import Examples.Groups.CCX+HH.NaturalP.Schema using (Gen ; gate₀ ; gate₁ ; gate₂ ; gate₃ ; _↥)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; inv)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (A⟦_⟧ ; A-cong ; A-↑ ; _↑ₐ ; _⊕_)
open import Examples.Groups.CCX+HH.NaturalP.Window using (high)
open import Examples.Groups.CCX+HH.NaturalP.Route4 using (stack)
open import Examples.Groups.CCX+HH.NaturalP.Transport using (cycA ; placed)

private
  variable
    n : ℕ

  inv-↑ : (w : Word (AGen n)) → inv (w ↑ₐ) ≡ inv w ↑ₐ
  inv-↑ [ g ]ʷ  = refl
  inv-↑ ε       = refl
  inv-↑ (u • v) = cong₂ _•_ (inv-↑ v) (inv-↑ u)

  inv-↑-act : (w : Word (AGen n)) (b : Bool) (s : State n) →
    A⟦ inv (w ↑ₐ) ⟧ (cons b s) ≈s cons b (A⟦ inv w ⟧ s)
  inv-↑-act w b s i = trans (cong (λ v → A⟦ v ⟧ (cons b s) i) (inv-↑ w)) (A-↑ (inv w) b s i)

------------------------------------------------------------------------
-- The cycle backwards

cycA-inv-act : ∀ n (b : Bool) (s : State n) → A⟦ inv (cycA n) ⟧ (cons b s) ≈s append n s b
cycA-inv-act zero    b s zero = refl
cycA-inv-act (suc n) b s i =
  trans (A-cong (inv (cycA n ↑ₐ)) sw i)
    (trans (inv-↑-act (cycA n) (s zero) (cons b (lower s)) i) (at i))
  where
  sw : C.swap (cons b s) ≈s cons (s zero) (cons b (lower s))
  sw zero          = refl
  sw (suc zero)    = refl
  sw (suc (suc j)) = refl
  at : ∀ i → cons (s zero) (A⟦ inv (cycA n) ⟧ (cons b (lower s))) i ≡ append (suc n) s b i
  at zero    = refl
  at (suc i) = cycA-inv-act n b (lower s) i

------------------------------------------------------------------------
-- Monotone windows

-- N⁻¹ sends the window state of h, under a colouring t, to increasing
-- indices; ι places h, tp reads the top four wires of a colouring.
GMono : ∀ n → (State 4 → State n) → (State n → State 4) → Word (AGen n) → Set
GMono n ι′ tp N = ∀ (t : State n) → tp t ≈s zeros → ∀ (y y′ : Fin 16) → y < y′ →
  idx n (A⟦ inv N ⟧ (ι′ (bits 4 y) ⊕ t)) < idx n (A⟦ inv N ⟧ (ι′ (bits 4 y′) ⊕ t))

private
  split0 : ∀ {n} (ι′ : State 4 → State n) (h : State 4) (t : State (suc n)) →
    cons false (ι′ h) ⊕ t ≈s cons (t zero) (ι′ h ⊕ lower t)
  split0 ι′ h t zero    = refl
  split0 ι′ h t (suc i) = refl

shift-g : ∀ {n} {ι′ : State 4 → State n} {tp : State n → State 4} {N : Word (AGen n)} →
  GMono n ι′ tp N → GMono (suc n) (λ h → cons false (ι′ h)) (λ t → tp (lower t)) (N ↑ₐ)
shift-g {n} {ι′} {tp} {N} m t z y y′ lt =
  subst₂ _<_ (sym (st y)) (sym (st y′)) (mono (select (alternating (2 ^ n)) (t zero)) (m (lower t) z y y′ lt))
  where
  st : ∀ y → idx (suc n) (A⟦ inv (N ↑ₐ) ⟧ (cons false (ι′ (bits 4 y)) ⊕ t)) ≡
    ι (select (alternating (2 ^ n)) (t zero)) (idx n (A⟦ inv N ⟧ (ι′ (bits 4 y) ⊕ lower t)))
  st y = idx-cong (suc n) (λ i → trans (A-cong (inv (N ↑ₐ)) (split0 ι′ (bits 4 y) t) i)
    (inv-↑-act N (t zero) (ι′ (bits 4 y) ⊕ lower t) i))

widen-g : ∀ {n} {ι′ : State 4 → State n} {tp : State n → State 4} {N : Word (AGen n)} →
  GMono n ι′ tp N → GMono (suc n) (λ h → cons false (ι′ h)) (λ t → tp (lower t)) ((N ↑ₐ) • cycA n)
widen-g {n} {ι′} {tp} {N} m t z y y′ lt =
  subst₂ _<_ (sym (st y)) (sym (st y′)) (mono (select (contiguous (2 ^ n)) (t zero)) (m (lower t) z y y′ lt))
  where
  st : ∀ y → idx (suc n) (A⟦ inv ((N ↑ₐ) • cycA n) ⟧ (cons false (ι′ (bits 4 y)) ⊕ t)) ≡
    ι (select (contiguous (2 ^ n)) (t zero)) (idx n (A⟦ inv N ⟧ (ι′ (bits 4 y) ⊕ lower t)))
  st y = trans (idx-cong (suc n) (λ i →
      trans (A-cong (inv (cycA n)) (λ j → trans (A-cong (inv (N ↑ₐ)) (split0 ι′ (bits 4 y) t) j)
                                      (inv-↑-act N (t zero) (ι′ (bits 4 y) ⊕ lower t) j)) i)
        (cycA-inv-act n (t zero) (A⟦ inv N ⟧ (ι′ (bits 4 y) ⊕ lower t)) i)))
    (idx-append n (A⟦ inv N ⟧ (ι′ (bits 4 y) ⊕ lower t)) (t zero))

-- The window and the top four wires of a colouring, at 4 + k + c wires.
ι₄ : ∀ k c → State 4 → State (₄₊ (k + (c + 0)))
ι₄ k c = stack (k + (c + 0)) zeros

top4 : ∀ k c → State (₄₊ (k + (c + 0))) → State 4
top4 k c t = high {0} c (high {c + 0} k t)

Mono : ∀ k c → Word (AGen (₄₊ (k + (c + 0)))) → Set
Mono k c = GMono (₄₊ (k + (c + 0))) (ι₄ k c) (top4 k c)

private
  base : GMono 4 (ι₄ 0 0) (top4 0 0) ε
  base t z y y′ lt = subst₂ (_<_ {16} {16}) (sym (e y)) (sym (e y′)) lt
    where
    e : ∀ y → idx 4 (bits 4 y ⊕ t) ≡ y
    e y = trans (idx-cong 4 {bits 4 y ⊕ t} {bits 4 y} (λ i → trans (cong (bits 4 y i xor_) (z i)) (xor-identityʳ _))) (idx-bits 4 y)

mono-placed : ∀ k c (x : Gen (₄₊ (k + (c + 0)))) → Mono k c (proj₁ (placed k c x))
mono-placed zero    zero    x         = base
mono-placed zero    (suc c) (gate₀ ())
mono-placed zero    (suc c) (gate₁ h) =
  widen-g {ι′ = ι₄ 0 c} {tp = top4 0 c} {N = proj₁ (placed zero c (gate₁ h))} (mono-placed zero c (gate₁ h))
mono-placed zero    (suc c) (gate₂ h) =
  widen-g {ι′ = ι₄ 0 c} {tp = top4 0 c} {N = proj₁ (placed zero c (gate₂ h))} (mono-placed zero c (gate₂ h))
mono-placed zero    (suc c) (gate₃ h) =
  widen-g {ι′ = ι₄ 0 c} {tp = top4 0 c} {N = proj₁ (placed zero c (gate₃ h))} (mono-placed zero c (gate₃ h))
mono-placed zero    (suc c) (g ↥)     =
  shift-g {ι′ = ι₄ 0 c} {tp = top4 0 c} {N = proj₁ (placed zero c g)} (mono-placed zero c g)
mono-placed (suc k) c       (gate₀ ())
mono-placed (suc k) c       (gate₁ h) =
  widen-g {ι′ = ι₄ k c} {tp = top4 k c} {N = proj₁ (placed k c (gate₁ h))} (mono-placed k c (gate₁ h))
mono-placed (suc k) c       (gate₂ h) =
  widen-g {ι′ = ι₄ k c} {tp = top4 k c} {N = proj₁ (placed k c (gate₂ h))} (mono-placed k c (gate₂ h))
mono-placed (suc k) c       (gate₃ h) =
  widen-g {ι′ = ι₄ k c} {tp = top4 k c} {N = proj₁ (placed k c (gate₃ h))} (mono-placed k c (gate₃ h))
mono-placed (suc k) c       (g ↥)     =
  shift-g {ι′ = ι₄ k c} {tp = top4 k c} {N = proj₁ (placed k c g)} (mono-placed k c g)
