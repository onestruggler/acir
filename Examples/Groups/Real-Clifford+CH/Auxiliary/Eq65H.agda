------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation (65) in full: the H-pattern branch
--
-- Where the four codes of H_[a,b] H_[c,d] have Figure 8's H-pattern —
-- a and a with one, the other, and both of two wires i < j flipped,
-- a being 0 there — Equation (35) does not apply and (36) or (37)
-- writes the letter instead as the standard pair between the two
-- halves of a word of encoded swaps and X gates (`Encoding.W₁`,
-- `W₂`).  Corollary A.7 turns any such writing into (65) once the
-- halves are Hadamard-free, inverse, and carry the standard pair to
-- the letter (`Eq65.Writing`), and that is a computation with their
-- signed permutations: by `NetSP` the swap network is a bit map, which
-- carries the wires i and j to 0 and 1 keeping the others in order
-- (`BitAlg.network`), the negations then clear the controls
-- (`BitAlg.negs`), so the four codes land on those of 0, 1, 3, 2 with
-- no sign, and each half undoes the other (`BitAlg.tele`).  With
-- `Eq65.eq65-35` for the other branch, that is (65) at every tuple of
-- four distinct indices (`eq65-full`), which is what everything built
-- on `Figure10.Eq65` assumed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65H (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_ ; not ; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List using (List ; [] ; _∷_ ; reverse)
open import Data.List.Properties using (reverse-involutive)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s ; _∸_ ; _≡ᵇ_ ; _<?_)
  renaming (_^_ to _^ℕ_ ; _+_ to _+ℕ_)
open import Data.Nat.Properties
  using (≤-pred ; <-trans ; ≤-<-trans ; ≮⇒≥ ; ≤-antisym ; <⇒≤ ; ≡ᵇ⇒≡)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; code-index ; index-code ; code-injective ; gray ; toBits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_ ; r36 ; r37)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (hh ; zz ; zx ; ∏ ; str₁ ; str₂ ; hpat ; distinct4 ; range↑ ; range↓
       ; E-Z ; E-CZ ; E-X ; E-swap ; ℰ ; ctrls ; negations↑ ; negations↓ ; swaps← ; swaps→
       ; HH₀₁₃₂ ; W₁ ; W₂)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m using (HFreeʷ ; gen ; nil ; cat ; hf-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; sp-inj ; idSP ; sgn≡ ; prm≡)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ⊙-cong to ⊛-cong ; ≐-trans to ≗-trans
          ; ≐-sym to ≗-sym ; ≐-refl to ≗-refl)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (spOp ; word-op ; word-scale ; ⟦_⟧ʷ ; spOp-⊙ ; spOp-id ; spOp-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m using (hfree-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃ ; gen-hh ; hh0132≡
       ; i₀≢i₁ ; i₃≢i₂)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A6 m using (Mpair ; Λ-op ; Λ-scale ; conj-at)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m as E65
  using (hh-scale ; hh-op ; Pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65 ; Sw ; S′w)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitAlg
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NetSP m
  using (bm ; bm-⊙ ; bm-id ; sp-∏ ; sp-Eswap ; sp-ℰ)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP n)

  idx : Bits n → Fin N
  idx = index n

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

  ≡ᵇ-refl : ∀ i → (i ≡ᵇ i) ≡ true
  ≡ᵇ-refl zero    = Eq.refl
  ≡ᵇ-refl (suc i) = ≡ᵇ-refl i

  ≡ᵇ-false : ∀ x y → x ≢ y → (x ≡ᵇ y) ≡ false
  ≡ᵇ-false x y ne with x ≡ᵇ y in e
  ... | true  = ⊥-elim (ne (≡ᵇ⇒≡ x y (Eq.subst T (Eq.sym e) tt)))
  ... | false = Eq.refl

  xor-f : ∀ x → x xor false ≡ x
  xor-f true  = Eq.refl
  xor-f false = Eq.refl

  xor-t : ∀ x → x xor true ≡ not x
  xor-t true  = Eq.refl
  xor-t false = Eq.refl

  -- A flipped bit, and the others.
  lk-same : ∀ p (x : Bits n) → p < n → lookupℕ p (flipℕ p x) ≡ not (lookupℕ p x)
  lk-same p x p<n = Eq.trans (lookup-flip p p x p<n)
                             (Eq.trans (Eq.cong (lookupℕ p x xor_) (≡ᵇ-refl p)) (xor-t _))

  lk-other : ∀ p w (x : Bits n) → p < n → w ≢ p → lookupℕ w (flipℕ p x) ≡ lookupℕ w x
  lk-other p w x p<n ne = Eq.trans (lookup-flip p w x p<n)
                                   (Eq.trans (Eq.cong (lookupℕ w x xor_) (≡ᵇ-false w p ne)) (xor-f _))

------------------------------------------------------------------------
-- The halves are Hadamard-free

hf-∏ : ∀ {A : Set} (F : A → W) (L : List A) → (∀ a → HFreeʷ (F a)) → HFreeʷ (∏ L F)
hf-∏ F []      h = nil
hf-∏ F (a ∷ L) h = cat (h a) (hf-∏ F L h)

hf-EZ : ∀ p → HFreeʷ (E-Z {m} p)
hf-EZ p = hf-∏ (λ c → zz {₃₊ m} (idx (str₁ {m} p c false true)) (idx (str₁ {m} p c true true)))
               (allBits (₁₊ m)) (λ c → gen (hf-zz _ _))

hf-ECZ : ∀ p → HFreeʷ (E-CZ {m} p)
hf-ECZ p = hf-∏ (λ c → zz {₃₊ m} (idx (str₂ {m} p c false true true)) (idx (str₂ {m} p c true true true)))
                (allBits m) (λ c → gen (hf-zz _ _))

hf-EX : ∀ p → HFreeʷ (E-X {m} p)
hf-EX p = cat (hf-EZ p)
              (hf-∏ (λ c → zx {₃₊ m} (idx (insertℕ p true c)) (idx (insertℕ p false c)) (idx (insertℕ p true c)))
                    (allBits (₂₊ m)) (λ c → hfree-zx _ _ _))

hf-Eswap : ∀ p → HFreeʷ (E-swap {m} p)
hf-Eswap p =
  cat (hf-ECZ p)
  (cat (hf-∏ F₁ (allBits (₁₊ m)) (λ c → hfree-zx _ _ _))
  (cat (hf-∏ F₂ (allBits (₁₊ m)) (λ c → hfree-zx _ _ _))
       (hf-∏ F₁ (allBits (₁₊ m)) (λ c → hfree-zx _ _ _))))
  where
  S : Bits (₁₊ m) → Bool → Bool → Bits n
  S c u t = insertℕ (suc p) u (insertℕ p t c)

  F₁ F₂ : Bits (₁₊ m) → W
  F₁ c = zx {₃₊ m} (idx (S c true true)) (idx (S c true false)) (idx (S c true true))
  F₂ c = zx {₃₊ m} (idx (S c false true)) (idx (S c false true)) (idx (S c true true))

hf-ℰ : ∀ b w → HFreeʷ (ℰ {m} b w)
hf-ℰ true  w = hf-EX w
hf-ℰ false w = nil

hf-swaps← : ∀ i j → HFreeʷ (swaps← {m} i j)
hf-swaps← i j = cat (hf-∏ (λ k → E-swap {m} k) (range↓ (suc i) j) hf-Eswap)
                    (hf-∏ (λ k → E-swap {m} k • E-swap {m} (suc k)) (range↓ 0 i)
                          (λ k → cat (hf-Eswap k) (hf-Eswap (suc k))))

hf-swaps→ : ∀ i j → HFreeʷ (swaps→ {m} i j)
hf-swaps→ i j = cat (hf-∏ (λ k → E-swap {m} (suc k) • E-swap {m} k) (range↑ 0 i)
                          (λ k → cat (hf-Eswap (suc k)) (hf-Eswap k)))
                    (hf-∏ (λ k → E-swap {m} k) (range↑ (suc i) j) hf-Eswap)

hf-neg↑ : ∀ x i j → HFreeʷ (negations↑ {m} x i j)
hf-neg↑ x i j = hf-∏ (λ w → ℰ {m} (lookupℕ (w ∸ 2) (ctrls {m} x i j)) w) (range↑ 2 n) (λ w → hf-ℰ _ w)

hf-neg↓ : ∀ x i j → HFreeʷ (negations↓ {m} x i j)
hf-neg↓ x i j = hf-∏ (λ w → ℰ {m} (lookupℕ (w ∸ 2) (ctrls {m} x i j)) w) (range↓ 2 n) (λ w → hf-ℰ _ w)

------------------------------------------------------------------------
-- The swap network as a bit map

module Net (i j : ℕ) (i<j : i < j) (j<n : j < n) where

  Φ← Φ→ : Bits n → Bits n
  Φ← x = run pairDn (range↓ 0 i) (run swapBits (range↓ (suc i) j) x)
  Φ→ y = run swapBits (range↑ (suc i) j) (run pairUp (range↑ 0 i) y)

  private
    j≤ : j ≤ ₂₊ m
    j≤ = ≤-pred j<n

    i≤ : i ≤ ₁₊ m
    i≤ = ≤-pred (≤-pred (≤-<-trans i<j j<n))

    i<n : i < n
    i<n = <-trans i<j j<n

    i≢j : i ≢ j
    i≢j e = <⇒≢′ i<j e
      where
      <⇒≢′ : ∀ {a b} → a < b → a ≢ b
      <⇒≢′ (s≤s p) Eq.refl = <⇒≢′ p Eq.refl

    j≢i : j ≢ i
    j≢i e = i≢j (Eq.sym e)

    sw1 : ∀ t → suc i ≤ t → t < j → sp (E-swap {m} t) ≗ bm (swapBits t)
    sw1 t _ t<j = sp-Eswap t (≤-<-trans t<j j<n)

    sw2 : ∀ t → 0 ≤ t → t < i → sp (E-swap {m} t • E-swap {m} (suc t)) ≗ bm (pairDn t)
    sw2 t _ t<i = ≗-trans (⊛-cong (sp-Eswap t (<-trans (≤-<-trans t<i i<j) j<n))
                                  (sp-Eswap (suc t) (≤-<-trans (s≤s t<i) (≤-<-trans i<j j<n))))
                          (bm-⊙ (swapBits t) (swapBits (suc t)))

    sw3 : ∀ t → 0 ≤ t → t < i → sp (E-swap {m} (suc t) • E-swap {m} t) ≗ bm (pairUp t)
    sw3 t _ t<i = ≗-trans (⊛-cong (sp-Eswap (suc t) (≤-<-trans (s≤s t<i) (≤-<-trans i<j j<n)))
                                  (sp-Eswap t (<-trans (≤-<-trans t<i i<j) j<n)))
                          (bm-⊙ (swapBits (suc t)) (swapBits t))

  sp-swaps← : sp (swaps← {m} i j) ≗ bm Φ←
  sp-swaps← =
    ≗-trans (⊛-cong (sp-∏ (λ k → E-swap {m} k) swapBits (range↓ (suc i) j) (all-range↓ (suc i) j sw1))
                    (sp-∏ (λ k → E-swap {m} k • E-swap {m} (suc k)) pairDn (range↓ 0 i)
                          (all-range↓ 0 i sw2)))
            (bm-⊙ (run swapBits (range↓ (suc i) j)) (run pairDn (range↓ 0 i)))

  sp-swaps→ : sp (swaps→ {m} i j) ≗ bm Φ→
  sp-swaps→ =
    ≗-trans (⊛-cong (sp-∏ (λ k → E-swap {m} (suc k) • E-swap {m} k) pairUp (range↑ 0 i)
                          (all-range↑ 0 i sw3))
                    (sp-∏ (λ k → E-swap {m} k) swapBits (range↑ (suc i) j) (all-range↑ (suc i) j sw1)))
            (bm-⊙ (run pairUp (range↑ 0 i)) (run swapBits (range↑ (suc i) j)))

  -- Back and forth.
  round : ∀ x → Φ→ (Φ← x) ≡ x
  round x = Eq.trans (Eq.cong (run swapBits (range↑ (suc i) j)) inner) outer
    where
    X : Bits n
    X = run swapBits (range↓ (suc i) j) x

    pinv : ∀ k y → pairUp k (pairDn k y) ≡ y
    pinv k y = Eq.trans (Eq.cong (swapBits k) (swap-invol (suc k) (swapBits k y))) (swap-invol k y)

    inner : run pairUp (range↑ 0 i) (run pairDn (range↓ 0 i) X) ≡ X
    inner = Eq.trans (Eq.cong (λ l → run pairUp l (run pairDn (range↓ 0 i) X))
                              (Eq.sym (reverse-involutive (range↑ 0 i))))
                     (tele pairDn pairUp (range↓ 0 i) pinv X)

    outer : run swapBits (range↑ (suc i) j) X ≡ x
    outer = Eq.trans (Eq.cong (λ l → run swapBits l X) (Eq.sym (reverse-involutive (range↑ (suc i) j))))
                     (tele swapBits swapBits (range↓ (suc i) j) (λ k y → swap-invol k y) x)

  -- On the four strings of a pattern at i and j.
  private
    net : ∀ x → Φ← x ≡ lookupℕ i x ∷ lookupℕ j x ∷ ctrls {m} x i j
    net x = network i j x i<j j≤

    ctrls-i : ∀ x → ctrls {m} (flipℕ i x) i j ≡ ctrls {m} x i j
    ctrls-i x = Eq.trans (Eq.cong (removeℕ i) (remove-flip-below i j x i<j j≤))
                         (remove-flip-same i (removeℕ j x) i≤)

    ctrls-j : ∀ x → ctrls {m} (flipℕ j x) i j ≡ ctrls {m} x i j
    ctrls-j x = Eq.cong (removeℕ i) (remove-flip-same j x j≤)

  N-x : ∀ x → lookupℕ i x ≡ false → lookupℕ j x ≡ false →
        Φ← x ≡ false ∷ false ∷ ctrls {m} x i j
  N-x x zi zj = Eq.trans (net x) (Eq.cong₂ (λ u v → u ∷ v ∷ ctrls {m} x i j) zi zj)

  N-i : ∀ x → lookupℕ i x ≡ false → lookupℕ j x ≡ false →
        Φ← (flipℕ i x) ≡ true ∷ false ∷ ctrls {m} x i j
  N-i x zi zj =
    Eq.trans (net (flipℕ i x))
      (Eq.cong₂ (λ u v → u ∷ v) (Eq.trans (lk-same i x i<n) (Eq.cong not zi))
        (Eq.cong₂ (λ u v → u ∷ v) (Eq.trans (lk-other i j x i<n j≢i) zj) (ctrls-i x)))

  N-j : ∀ x → lookupℕ i x ≡ false → lookupℕ j x ≡ false →
        Φ← (flipℕ j x) ≡ false ∷ true ∷ ctrls {m} x i j
  N-j x zi zj =
    Eq.trans (net (flipℕ j x))
      (Eq.cong₂ (λ u v → u ∷ v) (Eq.trans (lk-other j i x j<n i≢j) zi)
        (Eq.cong₂ (λ u v → u ∷ v) (Eq.trans (lk-same j x j<n) (Eq.cong not zj)) (ctrls-j x)))

  N-ij : ∀ x → lookupℕ i x ≡ false → lookupℕ j x ≡ false →
         Φ← (flipℕ i (flipℕ j x)) ≡ true ∷ true ∷ ctrls {m} x i j
  N-ij x zi zj =
    Eq.trans (net (flipℕ i (flipℕ j x)))
      (Eq.cong₂ (λ u v → u ∷ v)
        (Eq.trans (lk-same i (flipℕ j x) i<n) (Eq.cong not (Eq.trans (lk-other j i x j<n i≢j) zi)))
        (Eq.cong₂ (λ u v → u ∷ v)
          (Eq.trans (lk-other i j (flipℕ j x) i<n j≢i) (Eq.trans (lk-same j x j<n) (Eq.cong not zj)))
          (Eq.trans (ctrls-i (flipℕ j x)) (ctrls-j x))))

  N-ji : ∀ x → lookupℕ i x ≡ false → lookupℕ j x ≡ false →
         Φ← (flipℕ j (flipℕ i x)) ≡ true ∷ true ∷ ctrls {m} x i j
  N-ji x zi zj =
    Eq.trans (net (flipℕ j (flipℕ i x)))
      (Eq.cong₂ (λ u v → u ∷ v)
        (Eq.trans (lk-other j i (flipℕ i x) j<n i≢j) (Eq.trans (lk-same i x i<n) (Eq.cong not zi)))
        (Eq.cong₂ (λ u v → u ∷ v)
          (Eq.trans (lk-same j (flipℕ i x) j<n) (Eq.cong not (Eq.trans (lk-other i j x i<n j≢i) zj)))
          (Eq.trans (ctrls-j (flipℕ i x)) (ctrls-i x))))

------------------------------------------------------------------------
-- The negations as a bit map

module Negs (x : Bits n) (i j : ℕ) where

  private
    F : ℕ → Bits n → Bits n
    F w = cflip (lookupℕ (w ∸ 2) (ctrls {m} x i j)) w

  Ψ Ψ′ : Bits n → Bits n
  Ψ  = run F (range↑ 2 n)
  Ψ′ = run F (range↓ 2 n)

  sp-neg↑ : sp (negations↑ {m} x i j) ≗ bm Ψ
  sp-neg↑ = sp-∏ (λ w → ℰ {m} (lookupℕ (w ∸ 2) (ctrls {m} x i j)) w) F (range↑ 2 n)
                 (all-range↑ 2 n (λ t _ t<n → sp-ℰ (lookupℕ (t ∸ 2) (ctrls {m} x i j)) t t<n))

  sp-neg↓ : sp (negations↓ {m} x i j) ≗ bm Ψ′
  sp-neg↓ = sp-∏ (λ w → ℰ {m} (lookupℕ (w ∸ 2) (ctrls {m} x i j)) w) F (range↓ 2 n)
                 (all-range↓ 2 n (λ t _ t<n → sp-ℰ (lookupℕ (t ∸ 2) (ctrls {m} x i j)) t t<n))

  unneg : ∀ y → Ψ′ (Ψ y) ≡ y
  unneg y = tele F F (range↑ 2 n) (λ w z → cflip-invol (lookupℕ (w ∸ 2) (ctrls {m} x i j)) w z) y

  clear : ∀ u v → Ψ (u ∷ v ∷ ctrls {m} x i j) ≡ u ∷ v ∷ zeros (₁₊ m)
  clear u v = Eq.trans (negs (ctrls {m} x i j) (ctrls {m} x i j) u v)
                       (Eq.cong (λ r → u ∷ v ∷ r) (xorB-self (ctrls {m} x i j)))

------------------------------------------------------------------------
-- The codes of 0, 1, 3 and 2

private
  gray-zeros : ∀ k → gray (toBits k 0) ≡ zeros k
  gray-zeros zero          = Eq.refl
  gray-zeros (suc zero)    = Eq.refl
  gray-zeros (suc (suc k)) = Eq.cong (false ∷_) (gray-zeros (suc k))

code-i₀ : code n i₀ ≡ false ∷ false ∷ zeros (₁₊ m)
code-i₀ = Eq.trans (Eq.cong (λ k → gray (toBits n k)) toℕ-i₀) (gray-zeros n)

code-i₁ : code n i₁ ≡ true ∷ false ∷ zeros (₁₊ m)
code-i₁ = Eq.trans (Eq.cong (λ k → gray (toBits n k)) toℕ-i₁)
                   (Eq.cong (true ∷_) (gray-zeros (₂₊ m)))

code-i₂ : code n i₂ ≡ true ∷ true ∷ zeros (₁₊ m)
code-i₂ = Eq.trans (Eq.cong (λ k → gray (toBits n k)) toℕ-i₂)
                   (Eq.cong (λ r → true ∷ true ∷ r) (gray-zeros (₁₊ m)))

code-i₃ : code n i₃ ≡ false ∷ true ∷ zeros (₁₊ m)
code-i₃ = Eq.trans (Eq.cong (λ k → gray (toBits n k)) toℕ-i₃)
                   (Eq.cong (λ r → false ∷ true ∷ r) (gray-zeros (₁₊ m)))

private
  -- An index whose code the map sends to that of k is sent to k.
  lands : ∀ (φ : Bits n → Bits n) (z k : Fin N) → φ (code n z) ≡ code n k → prm (bm φ) z ≡ k
  lands φ z k e = Eq.trans (Eq.cong idx e) (index-code n k)

  HH≡Λ : HH₀₁₃₂ {m} ≡ Λ
  HH≡Λ = Eq.trans (Eq.sym (gen-hh i₀ i₁ i₃ i₂ i₀≢i₁ i₃≢i₂)) (Eq.sym hh0132≡)

------------------------------------------------------------------------
-- The writings of Equations (36) and (37)

module Writings (a b c d : Fin N)
                (ab : a ≢ b) (ac : a ≢ c) (ad : a ≢ d) (bc : b ≢ c) (bd : b ≢ d) (cd : c ≢ d)
                (pb pc : ℕ) (hp : hpat (code n a) (code n b) (code n c) (code n d) ≡ just (pb , pc))
  where

  open E65.Tuple a b c d ab ac ad bc bd cd using (Writing)

  private
    x : Bits n
    x = code n a

    H : HPat x (code n b) (code n c) (code n d) pb pc
    H = hpat-inv x (code n b) (code n c) (code n d) pb pc hp

    open Flips H

    pb≢pc′ : pb ≢ pc
    pb≢pc′ = pb≢pc (λ e → bc (code-injective n e))

    zb : lookupℕ pb x ≡ false
    zb = HPat.za H

    zc′ : lookupℕ pc x ≡ false
    zc′ = HPat.zc H

  -- (36): pc < pb, the lower wire i = pc and the upper j = pb.
  writing₁ : pc < pb → Writing
  writing₁ lt = record
    { A = A ; A′ = A′ ; hA = hA ; hA′ = hA′ ; inv = inv ; sem = sem ; syn = syn }
    where
    i j : ℕ
    i = pc
    j = pb

    open Net i j lt pb<n
    open Negs x i j

    A A′ : W
    A  = swaps← {m} i j • (E-swap {m} 0 • negations↑ {m} x i j)
    A′ = negations↓ {m} x i j • (E-swap {m} 0 • swaps→ {m} i j)

    hA : HFreeʷ A
    hA = cat (hf-swaps← i j) (cat (hf-Eswap 0) (hf-neg↑ x i j))

    hA′ : HFreeʷ A′
    hA′ = cat (hf-neg↓ x i j) (cat (hf-Eswap 0) (hf-swaps→ i j))

    φ φ′ : Bits n → Bits n
    φ  y = Ψ (swapBits 0 (Φ← y))
    φ′ y = Φ→ (swapBits 0 (Ψ′ y))

    spA : sp A ≗ bm φ
    spA = ≗-trans (⊛-cong sp-swaps← (⊛-cong (sp-Eswap 0 (s≤s (s≤s z≤n))) sp-neg↑))
                  (≗-trans (⊛-cong (≗-refl {bm Φ←}) (bm-⊙ (swapBits 0) Ψ))
                           (bm-⊙ Φ← (λ y → Ψ (swapBits 0 y))))

    spA′ : sp A′ ≗ bm φ′
    spA′ = ≗-trans (⊛-cong sp-neg↓ (⊛-cong (sp-Eswap 0 (s≤s (s≤s z≤n))) sp-swaps→))
                   (≗-trans (⊛-cong (≗-refl {bm Ψ′}) (bm-⊙ (swapBits 0) Φ→))
                            (bm-⊙ Ψ′ (λ y → Φ→ (swapBits 0 y))))

    rt : ∀ y → φ′ (φ y) ≡ y
    rt y = Eq.trans (Eq.cong (λ w → Φ→ (swapBits 0 w)) (unneg (swapBits 0 (Φ← y))))
             (Eq.trans (Eq.cong Φ→ (swap-invol 0 (Φ← y))) (round y))

    inv-sp : sp A ⊛ sp A′ ≗ idSP
    inv-sp = ≗-trans (⊛-cong spA spA′) (≗-trans (bm-⊙ φ φ′) (bm-id (λ y → φ′ (φ y)) rt))

    sp-id : (spOp (sp A) ⊙ spOp (sp A′)) ≐ Idₒ
    sp-id = ≐-trans (≐-sym (spOp-⊙ (sp A) (sp A′))) (≐-trans (spOp-cong inv-sp) spOp-id)

    inv : ⟦ A • A′ ⟧ʷ ~ ⟦ ε ⟧ʷ
    inv = ~-reflexive (Eq.cong₂ _+ℕ_ (word-scale hA) (word-scale hA′))
                      (≐-trans (⊙-cong (word-op hA) (word-op hA′)) sp-id)

    -- Where the four codes land.
    im-a : φ x ≡ code n i₀
    im-a = Eq.trans (Eq.cong (λ y → Ψ (swapBits 0 y)) (N-x x zc′ zb))
                    (Eq.trans (clear false false) (Eq.sym code-i₀))

    im-b : φ (code n b) ≡ code n i₁
    im-b = Eq.trans (Eq.cong (λ y → Ψ (swapBits 0 (Φ← y))) b-flip)
             (Eq.trans (Eq.cong (λ y → Ψ (swapBits 0 y)) (N-j x zc′ zb))
                       (Eq.trans (clear true false) (Eq.sym code-i₁)))

    im-c : φ (code n c) ≡ code n i₃
    im-c = Eq.trans (Eq.cong (λ y → Ψ (swapBits 0 (Φ← y))) c-flip)
             (Eq.trans (Eq.cong (λ y → Ψ (swapBits 0 y)) (N-i x zc′ zb))
                       (Eq.trans (clear false true) (Eq.sym code-i₃)))

    im-d : φ (code n d) ≡ code n i₂
    im-d = Eq.trans (Eq.cong (λ y → Ψ (swapBits 0 (Φ← y))) (d-flip pb≢pc′))
             (Eq.trans (Eq.cong (λ y → Ψ (swapBits 0 y)) (N-ji x zc′ zb))
                       (Eq.trans (clear true true) (Eq.sym code-i₂)))

    pr : ∀ (z k : Fin N) → φ (code n z) ≡ code n k → prm (sp A) z ≡ k
    pr z k e = Eq.trans (prm≡ spA z) (lands φ z k e)

    sg : ∀ (z : Fin N) → sgn (sp A) z ≡ false
    sg z = sgn≡ spA z

    conj : (spOp (sp A) ⊙ (Mpair ⊙ spOp (sp A′))) ≐ Pair a b c d
    conj = conj-at A A′ (sp-inj A′) inv-sp a b c d
                   (pr a i₀ im-a) (pr b i₁ im-b) (pr c i₃ im-c) (pr d i₂ im-d)
                   (sg a) (sg b) (sg c) (sg d)

    scale : proj₁ ⟦ A • (Λ • A′) ⟧ʷ ≡ proj₁ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    scale = Eq.trans (Eq.cong₂ _+ℕ_ (word-scale hA) (Eq.cong₂ _+ℕ_ Λ-scale (word-scale hA′)))
                     (Eq.sym (hh-scale a b c d ab cd))

    matEq : proj₂ ⟦ A • (Λ • A′) ⟧ʷ ≐ proj₂ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    matEq = ≐-trans (≐-trans (⊙-cong (word-op hA) (⊙-cong Λ-op (word-op hA′))) conj)
                    (≐-sym (hh-op a b c d ab cd))

    sem : ⟦ A • (Λ • A′) ⟧ʷ ~ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    sem = ~-reflexive scale matEq

    syn : hh {₃₊ m} a b c d ≈ A • (Λ • A′)
    syn = trans (axiom (r36 a b c d pb pc hp lt))
            (trans (refl≡ (Eq.cong (λ h → swaps← {m} i j • (E-swap {m} 0 • (negations↑ {m} x i j • (h • A′))))
                                   HH≡Λ))
                   (trans (back (swaps← {m} i j) (sym assoc)) (sym assoc)))

  -- (37): pb < pc, the lower wire i = pb and the upper j = pc.
  writing₂ : pb < pc → Writing
  writing₂ lt = record
    { A = A ; A′ = A′ ; hA = hA ; hA′ = hA′ ; inv = inv ; sem = sem ; syn = syn }
    where
    i j : ℕ
    i = pb
    j = pc

    open Net i j lt pc<n
    open Negs x i j

    A A′ : W
    A  = swaps← {m} i j • negations↑ {m} x i j
    A′ = negations↓ {m} x i j • swaps→ {m} i j

    hA : HFreeʷ A
    hA = cat (hf-swaps← i j) (hf-neg↑ x i j)

    hA′ : HFreeʷ A′
    hA′ = cat (hf-neg↓ x i j) (hf-swaps→ i j)

    φ φ′ : Bits n → Bits n
    φ  y = Ψ (Φ← y)
    φ′ y = Φ→ (Ψ′ y)

    spA : sp A ≗ bm φ
    spA = ≗-trans (⊛-cong sp-swaps← sp-neg↑) (bm-⊙ Φ← Ψ)

    spA′ : sp A′ ≗ bm φ′
    spA′ = ≗-trans (⊛-cong sp-neg↓ sp-swaps→) (bm-⊙ Ψ′ Φ→)

    rt : ∀ y → φ′ (φ y) ≡ y
    rt y = Eq.trans (Eq.cong Φ→ (unneg (Φ← y))) (round y)

    inv-sp : sp A ⊛ sp A′ ≗ idSP
    inv-sp = ≗-trans (⊛-cong spA spA′) (≗-trans (bm-⊙ φ φ′) (bm-id (λ y → φ′ (φ y)) rt))

    sp-id : (spOp (sp A) ⊙ spOp (sp A′)) ≐ Idₒ
    sp-id = ≐-trans (≐-sym (spOp-⊙ (sp A) (sp A′))) (≐-trans (spOp-cong inv-sp) spOp-id)

    inv : ⟦ A • A′ ⟧ʷ ~ ⟦ ε ⟧ʷ
    inv = ~-reflexive (Eq.cong₂ _+ℕ_ (word-scale hA) (word-scale hA′))
                      (≐-trans (⊙-cong (word-op hA) (word-op hA′)) sp-id)

    im-a : φ x ≡ code n i₀
    im-a = Eq.trans (Eq.cong Ψ (N-x x zb zc′)) (Eq.trans (clear false false) (Eq.sym code-i₀))

    im-b : φ (code n b) ≡ code n i₁
    im-b = Eq.trans (Eq.cong (λ y → Ψ (Φ← y)) b-flip)
             (Eq.trans (Eq.cong Ψ (N-i x zb zc′)) (Eq.trans (clear true false) (Eq.sym code-i₁)))

    im-c : φ (code n c) ≡ code n i₃
    im-c = Eq.trans (Eq.cong (λ y → Ψ (Φ← y)) c-flip)
             (Eq.trans (Eq.cong Ψ (N-j x zb zc′)) (Eq.trans (clear false true) (Eq.sym code-i₃)))

    im-d : φ (code n d) ≡ code n i₂
    im-d = Eq.trans (Eq.cong (λ y → Ψ (Φ← y)) (d-flip pb≢pc′))
             (Eq.trans (Eq.cong Ψ (N-ij x zb zc′)) (Eq.trans (clear true true) (Eq.sym code-i₂)))

    pr : ∀ (z k : Fin N) → φ (code n z) ≡ code n k → prm (sp A) z ≡ k
    pr z k e = Eq.trans (prm≡ spA z) (lands φ z k e)

    sg : ∀ (z : Fin N) → sgn (sp A) z ≡ false
    sg z = sgn≡ spA z

    conj : (spOp (sp A) ⊙ (Mpair ⊙ spOp (sp A′))) ≐ Pair a b c d
    conj = conj-at A A′ (sp-inj A′) inv-sp a b c d
                   (pr a i₀ im-a) (pr b i₁ im-b) (pr c i₃ im-c) (pr d i₂ im-d)
                   (sg a) (sg b) (sg c) (sg d)

    scale : proj₁ ⟦ A • (Λ • A′) ⟧ʷ ≡ proj₁ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    scale = Eq.trans (Eq.cong₂ _+ℕ_ (word-scale hA) (Eq.cong₂ _+ℕ_ Λ-scale (word-scale hA′)))
                     (Eq.sym (hh-scale a b c d ab cd))

    matEq : proj₂ ⟦ A • (Λ • A′) ⟧ʷ ≐ proj₂ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    matEq = ≐-trans (≐-trans (⊙-cong (word-op hA) (⊙-cong Λ-op (word-op hA′))) conj)
                    (≐-sym (hh-op a b c d ab cd))

    sem : ⟦ A • (Λ • A′) ⟧ʷ ~ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    sem = ~-reflexive scale matEq

    syn : hh {₃₊ m} a b c d ≈ A • (Λ • A′)
    syn = trans (axiom (r37 a b c d pb pc hp lt))
            (trans (refl≡ (Eq.cong (λ h → swaps← {m} i j • (negations↑ {m} x i j • (h • A′))) HH≡Λ))
                   (sym assoc))

  -- The two wires differ.
  apart : pb ≢ pc
  apart = pb≢pc′

------------------------------------------------------------------------
-- Equation (65)

eq65-full : Eq65
eq65-full a b c d ab ac ad bc bd cd = main (hpat (code n a) (code n b) (code n c) (code n d)) Eq.refl
  where
  open E65.Tuple a b c d ab ac ad bc bd cd using (eq65-from ; eq65-35)

  nb : ∀ {x y : Fin N} → x ≢ y → (toℕ x ≡ᵇ toℕ y) ≡ false
  nb ne = ≡ᵇ-false _ _ (λ e → ne (toℕ-injective e))

  d4 : distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ true
  d4 rewrite nb ab | nb ac | nb ad | nb bc | nb bd | nb cd = Eq.refl

  main : ∀ (r : Maybe (ℕ × ℕ)) → hpat (code n a) (code n b) (code n c) (code n d) ≡ r →
         hh {₃₊ m} a b c d ≈ Sw a b c d • (Λ • S′w a b c d)
  main nothing          hp = eq65-35 d4 hp
  main (just (pb , pc)) hp = pick (pc <? pb) (pb <? pc)
    where
    module Wr = Writings a b c d ab ac ad bc bd cd pb pc hp

    pick : Dec (pc < pb) → Dec (pb < pc) → hh {₃₊ m} a b c d ≈ Sw a b c d • (Λ • S′w a b c d)
    pick (yes lt) _        = eq65-from (Wr.writing₁ lt)
    pick (no _)   (yes lt) = eq65-from (Wr.writing₂ lt)
    pick (no n₁)  (no n₂)  = ⊥-elim (Wr.apart (≤-antisym (≮⇒≥ n₁) (≮⇒≥ n₂)))
