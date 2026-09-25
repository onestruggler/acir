------------------------------------------------------------------------
-- Presentations of groups
--
-- The sign pair on 3 and 2, and why it passes a Hadamard pair
--
-- Of the three generators Lemma A.6 states its form over, Figure 8
-- carries two across H_[0,1] H_[3,2] outright — the sign pair on 0 and
-- 1 by (39) and the double exchange by (44).  The third, the sign pair
-- on 3 and 2, it does not: but the double exchange conjugates one sign
-- pair into the other, so it passes too.
--
-- That the two are conjugate is a fact about signed permutations, and
-- Corollary A.5 turns it into an equivalence: pushing the signs left
-- through the exchanges renames their indices by the exchange, and
-- what is left of the exchanges cancels, being two involutions on
-- disjoint pairs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens (m : ℕ) where

open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_ ; toℕ-inject≤)
open import Relation.Nullary using (yes ; no)
open import Data.Nat using (suc) renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
  using (GenP ; −1−1 ; XX ; HH)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (zz ; xx ; hh ; zzℕ ; xxℕ ; hhℕ ; toFin)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m
  using (toFin-toℕ ; zzℕ-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; nil ; cat ; HFree ; hf-zz ; hf-xx ; gen-xx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; NEG ; SWP ; idSP ; sp ; sp-xx ; swapF ; swapF-a ; swapF-b ; swapF-o
       ; SWP-NEG ; SWP-invol ; SWP-comm ; NEG-invol ; NEG-comm
       ; ⊙-assoc ; ⊙-cong ; ⊙-idʳ
       ; hop ; drop ; neg≡ ; ≐-refl ; ≐-sym ; ≐-trans)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- The four indices the pair is written over

i₀ i₁ i₂ i₃ : Fin N
i₀ = fin8 {m} ₀
i₁ = fin8 {m} ₁
i₂ = fin8 {m} ₂
i₃ = fin8 {m} ₃

toℕ-i₀ : toℕ i₀ ≡ 0
toℕ-i₀ = toℕ-inject≤ ₀ _

toℕ-i₁ : toℕ i₁ ≡ 1
toℕ-i₁ = toℕ-inject≤ ₁ _

toℕ-i₂ : toℕ i₂ ≡ 2
toℕ-i₂ = toℕ-inject≤ ₂ _

toℕ-i₃ : toℕ i₃ ≡ 3
toℕ-i₃ = toℕ-inject≤ ₃ _

private
  -- Distinctness, read off the numerals.
  diff : ∀ {a b : Fin N} {x y : ℕ} → toℕ a ≡ x → toℕ b ≡ y → x ≢ y → a ≢ b
  diff ea eb ne e = ne (Eq.trans (Eq.sym ea) (Eq.trans (Eq.cong toℕ e) eb))

i₀≢i₁ : i₀ ≢ i₁
i₀≢i₁ = diff toℕ-i₀ toℕ-i₁ (λ ())

i₀≢i₂ : i₀ ≢ i₂
i₀≢i₂ = diff toℕ-i₀ toℕ-i₂ (λ ())

i₀≢i₃ : i₀ ≢ i₃
i₀≢i₃ = diff toℕ-i₀ toℕ-i₃ (λ ())

i₁≢i₂ : i₁ ≢ i₂
i₁≢i₂ = diff toℕ-i₁ toℕ-i₂ (λ ())

i₁≢i₃ : i₁ ≢ i₃
i₁≢i₃ = diff toℕ-i₁ toℕ-i₃ (λ ())

i₂≢i₃ : i₂ ≢ i₃
i₂≢i₃ = diff toℕ-i₂ toℕ-i₃ (λ ())

private
  ≢sym : ∀ {a b : Fin N} → a ≢ b → b ≢ a
  ≢sym ne e = ne (Eq.sym e)

------------------------------------------------------------------------
-- The words

Xw : W
Xw = xx {₃₊ m} i₀ i₃ i₁ i₂

Z₀₁ Z₃₂ : W
Z₀₁ = zz {₃₊ m} i₀ i₁
Z₃₂ = zz {₃₊ m} i₃ i₂

-- Figure 8 states (39) and (44) over numerals; these are the same
-- words, the indices decided.

xxℕ-xx : ∀ (a b c d : Fin N) →
         xxℕ {₃₊ m} (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ xx a b c d
xxℕ-xx a b c d
  rewrite toFin-toℕ a | toFin-toℕ b | toFin-toℕ c | toFin-toℕ d = Eq.refl

zz01≡ : zzℕ {₃₊ m} 0 1 ≡ Z₀₁
zz01≡ = Eq.trans (Eq.cong₂ (zzℕ {₃₊ m}) (Eq.sym toℕ-i₀) (Eq.sym toℕ-i₁))
                 (zzℕ-zz i₀ i₁)

zz32≡ : zzℕ {₃₊ m} 3 2 ≡ Z₃₂
zz32≡ = Eq.trans (Eq.cong₂ (zzℕ {₃₊ m}) (Eq.sym toℕ-i₃) (Eq.sym toℕ-i₂))
                 (zzℕ-zz i₃ i₂)

-- The Hadamard pair itself, as a letter.
gen-hh : ∀ (a b c d : Fin N) .(ni : a ≢ b) .(ni′ : c ≢ d) →
         [ HH {₃₊ m} a b c d ni ni′ ]ʷ ≡ hh {₃₊ m} a b c d
gen-hh a b c d ni ni′ with a ≟ b | c ≟ d
... | yes e | _     = ⊥-elim-irr (ni e)
... | no  _ | yes e = ⊥-elim-irr (ni′ e)
... | no  _ | no  _ = Eq.refl

hhℕ-hh : ∀ (a b c d : Fin N) →
         hhℕ {₃₊ m} (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ hh a b c d
hhℕ-hh a b c d
  rewrite toFin-toℕ a | toFin-toℕ b | toFin-toℕ c | toFin-toℕ d = Eq.refl

i₃≢i₂ : i₃ ≢ i₂
i₃≢i₂ = ≢sym i₂≢i₃

Λw : W
Λw = [ HH {₃₊ m} i₀ i₁ i₃ i₂ i₀≢i₁ i₃≢i₂ ]ʷ

hh0132≡ : hhℕ {₃₊ m} 0 1 3 2 ≡ Λw
hh0132≡ = Eq.sym
  (Eq.trans (gen-hh i₀ i₁ i₃ i₂ i₀≢i₁ i₃≢i₂)
  (Eq.trans (Eq.sym (hhℕ-hh i₀ i₁ i₃ i₂))
  (Eq.trans (Eq.cong₂ (λ x y → hhℕ {₃₊ m} x y (toℕ i₃) (toℕ i₂)) toℕ-i₀ toℕ-i₁)
            (Eq.cong₂ (λ x y → hhℕ {₃₊ m} 0 1 x y) toℕ-i₃ toℕ-i₂))))

xx0312≡ : xxℕ {₃₊ m} 0 3 1 2 ≡ Xw
xx0312≡ = Eq.trans (Eq.cong₂ (λ x y → xxℕ {₃₊ m} x y 1 2)
                             (Eq.sym toℕ-i₀) (Eq.sym toℕ-i₃))
          (Eq.trans (Eq.cong₂ (λ x y → xxℕ {₃₊ m} (toℕ i₀) (toℕ i₃) x y)
                              (Eq.sym toℕ-i₁) (Eq.sym toℕ-i₂))
                    (xxℕ-xx i₀ i₃ i₁ i₂))

------------------------------------------------------------------------
-- They are conjugate as signed permutations

private
  -- Pushing one sign left through one exchange renames its index.
  hopN : ∀ (a b c : Fin N) (h : SP) →
         SWP a b ⊛ (NEG c ⊛ h) ≗ NEG (swapF a b c) ⊛ (SWP a b ⊛ h)
  hopN a b c h = hop (SWP a b) (NEG c) (SWP a b) (NEG (swapF a b c)) h (SWP-NEG a b c)

  fix₃ : swapF i₀ i₃ i₀ ≡ i₃
  fix₃ = swapF-a i₀ i₃

  fix₂ : swapF i₁ i₂ i₁ ≡ i₂
  fix₂ = swapF-a i₁ i₂

  keep₀ : swapF i₁ i₂ i₀ ≡ i₀
  keep₀ = swapF-o i₁ i₂ i₀ i₀≢i₁ i₀≢i₂

  keep₂ : swapF i₀ i₃ i₂ ≡ i₂
  keep₂ = swapF-o i₀ i₃ i₂ (≢sym i₀≢i₂) i₂≢i₃

  -- The exchanges left over cancel: two involutions on disjoint pairs.
  swaps : SWP i₀ i₃ ⊛ (SWP i₁ i₂ ⊛ (SWP i₀ i₃ ⊛ SWP i₁ i₂)) ≗ idSP
  swaps =
    ≐-trans (⊙-cong (≐-refl {SWP i₀ i₃})
                    (hop (SWP i₁ i₂) (SWP i₀ i₃) (SWP i₁ i₂) (SWP i₀ i₃) (SWP i₁ i₂)
                         (SWP-comm i₁ i₂ i₀ i₃ i₀≢i₁ i₀≢i₂
                                   (≢sym i₁≢i₃) (≢sym i₂≢i₃))))
            (≐-trans (drop (SWP i₀ i₃) (SWP i₀ i₃) (SWP i₁ i₂ ⊛ SWP i₁ i₂)
                           (SWP-invol i₀ i₃))
                     (SWP-invol i₁ i₂))

private
  s t : SP
  s = SWP i₀ i₃
  t = SWP i₁ i₂

  A : SP
  A = s ⊛ t

  -- Flatten the two exchanges and the two signs.
  step₁ : A ⊛ ((NEG i₀ ⊛ NEG i₁) ⊛ A) ≗ s ⊛ (t ⊛ (NEG i₀ ⊛ (NEG i₁ ⊛ A)))
  step₁ =
    ≐-trans (⊙-assoc s t ((NEG i₀ ⊛ NEG i₁) ⊛ A))
            (⊙-cong (≐-refl {s})
                    (⊙-cong (≐-refl {t}) (⊙-assoc (NEG i₀) (NEG i₁) A)))

  -- The outer sign crosses the exchange that does not see it, …
  step₂ : t ⊛ (NEG i₀ ⊛ (NEG i₁ ⊛ A)) ≗ NEG i₀ ⊛ (t ⊛ (NEG i₁ ⊛ A))
  step₂ = ≐-trans (hopN i₁ i₂ i₀ (NEG i₁ ⊛ A))
                  (⊙-cong (neg≡ keep₀) (≐-refl {t ⊛ (NEG i₁ ⊛ A)}))

  -- … then the one that renames it to 3.
  step₃ : s ⊛ (NEG i₀ ⊛ (t ⊛ (NEG i₁ ⊛ A))) ≗ NEG i₃ ⊛ (s ⊛ (t ⊛ (NEG i₁ ⊛ A)))
  step₃ = ≐-trans (hopN i₀ i₃ i₀ (t ⊛ (NEG i₁ ⊛ A)))
                  (⊙-cong (neg≡ fix₃) (≐-refl {s ⊛ (t ⊛ (NEG i₁ ⊛ A))}))

  -- The inner sign does the same, coming out on 2; what is left of the
  -- exchanges cancels.
  step₄ : t ⊛ (NEG i₁ ⊛ A) ≗ NEG i₂ ⊛ (t ⊛ A)
  step₄ = ≐-trans (hopN i₁ i₂ i₁ A) (⊙-cong (neg≡ fix₂) (≐-refl {t ⊛ A}))

  step₅ : s ⊛ (NEG i₂ ⊛ (t ⊛ A)) ≗ NEG i₂ ⊛ (s ⊛ (t ⊛ A))
  step₅ = ≐-trans (hopN i₀ i₃ i₂ (t ⊛ A))
                  (⊙-cong (neg≡ keep₂) (≐-refl {s ⊛ (t ⊛ A)}))

  inner : s ⊛ (t ⊛ (NEG i₁ ⊛ A)) ≗ NEG i₂
  inner =
    ≐-trans (⊙-cong (≐-refl {s}) step₄)
    (≐-trans step₅
    (≐-trans (⊙-cong (≐-refl {NEG i₂}) swaps) (⊙-idʳ (NEG i₂))))

sp-Xw : sp Xw ≗ A
sp-Xw = sp-xx i₀ i₃ i₁ i₂ i₀≢i₃ i₁≢i₂

conj-sp : sp (Xw • (Z₀₁ • Xw)) ≗ sp Z₃₂
conj-sp =
  ≐-trans (⊙-cong sp-Xw (⊙-cong (≐-refl {NEG i₀ ⊛ NEG i₁}) sp-Xw))
  (≐-trans step₁
  (≐-trans (⊙-cong (≐-refl {s}) step₂)
  (≐-trans step₃ (⊙-cong (≐-refl {NEG i₃}) inner))))

------------------------------------------------------------------------
-- So the sign pair on 3 and 2 is the one on 0 and 1, conjugated

hfree-X : HFreeʷ Xw
hfree-X = Eq.subst HFreeʷ (gen-xx i₀ i₃ i₁ i₂ i₀≢i₃ i₁≢i₂)
                   (gen (hf-xx i₀ i₃ i₁ i₂ i₀≢i₃ i₁≢i₂))

hfree-Z₀₁ : HFreeʷ Z₀₁
hfree-Z₀₁ = gen (hf-zz i₀ i₁)

hfree-Z₃₂ : HFreeʷ Z₃₂
hfree-Z₃₂ = gen (hf-zz i₃ i₂)

conj-≈ : PB._≈_ (m P,_===_) (Xw • (Z₀₁ • Xw)) Z₃₂
conj-≈ = A5-full (cat hfree-X (cat hfree-Z₀₁ hfree-X)) hfree-Z₃₂ conj-sp

------------------------------------------------------------------------
-- All three are involutions
--
-- Corollary A.5 again: each squares to the identity permutation, and
-- the empty word is the only normal form that does.

private
  -- Two signs on distinct indices commute and each squares away.
  zz-sq : ∀ (a b : Fin N) → (NEG a ⊛ NEG b) ⊛ (NEG a ⊛ NEG b) ≗ idSP
  zz-sq a b =
    ≐-trans (⊙-assoc (NEG a) (NEG b) (NEG a ⊛ NEG b))
    (≐-trans (⊙-cong (≐-refl {NEG a})
               (hop (NEG b) (NEG a) (NEG b) (NEG a) (NEG b) (NEG-comm b a)))
    (≐-trans (drop (NEG a) (NEG a) (NEG b ⊛ NEG b) (NEG-invol a))
             (NEG-invol b)))

  sq : ∀ {u : W} → HFreeʷ u → sp (u • u) ≗ idSP → PB._≈_ (m P,_===_) (u • u) ε
  sq h e = A5-full (cat h h) nil e

-- The double exchange is an involution, already as a signed
-- permutation.
Xw-sp-invol : sp Xw ⊛ sp Xw ≗ idSP
Xw-sp-invol = ≐-trans (⊙-cong sp-Xw sp-Xw) (≐-trans (⊙-assoc s t A) swaps)

Xw-invol : PB._≈_ (m P,_===_) (Xw • Xw) ε
Xw-invol = sq hfree-X Xw-sp-invol

Z₀₁-invol : PB._≈_ (m P,_===_) (Z₀₁ • Z₀₁) ε
Z₀₁-invol = sq hfree-Z₀₁ (zz-sq i₀ i₁)

Z₃₂-invol : PB._≈_ (m P,_===_) (Z₃₂ • Z₃₂) ε
Z₃₂-invol = sq hfree-Z₃₂ (zz-sq i₃ i₂)
