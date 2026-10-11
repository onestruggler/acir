------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoding preserves the semantics of H and CH (Definition 8.2)
--
-- The letters of E(H on wire p) are the two-level Hadamards on the
-- pairs of basis vectors that differ only at wire p, each pair once;
-- for CH, on the pairs whose control bit is set.  Their product is
-- computed through an invariant over the contexts processed so far:
-- on the vectors already covered it is the Hadamard of wire p, on the
-- others the identity, each up to the power of √2 the factors so far
-- contribute; one two-level Hadamard on an uncovered pair moves the
-- invariant one step.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.EncodingSemantics.Hadamard where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ ; ∨-identityʳ ; ∧-zeroʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List ; [] ; _∷_ ; foldr)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n) renaming (_+_ to _+ℕ_ ; _^_ to _^ℕ_)
open import Data.Nat.Properties using (≤-pred ; ≤-refl ; ≤-trans ; n≤1+n)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (code ; index ; code-index ; index-injective)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB ; hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
open import Examples.Groups.Real-Clifford+CH.Auxiliary.WireForms
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Encoding
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Products
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Strings

import Data.Fin.Properties as FP

------------------------------------------------------------------------
-- Booleans, scalars and δ

private
  true≢false : true ≢ false
  true≢false ()

  if-true : ∀ {A : Set} {b : Bool} (u v : A) → b ≡ true → (if b then u else v) ≡ u
  if-true u v Eq.refl = Eq.refl

  if-false : ∀ {A : Set} {b : Bool} (u v : A) → b ≡ false → (if b then u else v) ≡ v
  if-false u v Eq.refl = Eq.refl

  bool-cases : ∀ {P : Set} (b : Bool) → (b ≡ true → P) → (b ≡ false → P) → P
  bool-cases true  t f = t Eq.refl
  bool-cases false t f = f Eq.refl

  -- Where a disjunction of five is true.
  or1 : ∀ a b c d e → b ≡ true → ((a ∨ b ∨ c) ∨ d ∨ e) ≡ true
  or1 a b c d e eb =
    Eq.trans (Eq.cong (λ u → (a ∨ u ∨ c) ∨ d ∨ e) eb) (Eq.cong (_∨ (d ∨ e)) (∨-zeroʳ a))

  or2 : ∀ a b c d e → c ≡ true → ((a ∨ b ∨ c) ∨ d ∨ e) ≡ true
  or2 a b c d e ec =
    Eq.trans (Eq.cong (λ u → (a ∨ b ∨ u) ∨ d ∨ e) ec)
      (Eq.trans (Eq.cong (λ u → (a ∨ u) ∨ d ∨ e) (∨-zeroʳ b)) (Eq.cong (_∨ (d ∨ e)) (∨-zeroʳ a)))

  or3 : ∀ a b c d e → d ≡ true → ((a ∨ b ∨ c) ∨ d ∨ e) ≡ true
  or3 a b c d e ed =
    Eq.trans (Eq.cong (λ u → (a ∨ b ∨ c) ∨ u ∨ e) ed) (∨-zeroʳ (a ∨ b ∨ c))

  or4 : ∀ a b c d e → e ≡ true → ((a ∨ b ∨ c) ∨ d ∨ e) ≡ true
  or4 a b c d e ee =
    Eq.trans (Eq.cong (λ u → (a ∨ b ∨ c) ∨ d ∨ u) ee)
      (Eq.trans (Eq.cong ((a ∨ b ∨ c) ∨_) (∨-zeroʳ d)) (∨-zeroʳ (a ∨ b ∨ c)))

  -- Powers of √2.
  √2^1 : √2^ 1 ≡ √2
  √2^1 = Eq.refl

  √2^-suc : ∀ f → √2^ (suc f) ≡ √2 * √2^ f
  √2^-suc f = strict-id (√2 * √2^ f)

  -- Rearrangements of products.
  swap-left : ∀ x y z → x * (y * z) ≡ y * (x * z)
  swap-left x y z =
    Eq.trans (Eq.sym (*-assoc x y z)) (Eq.trans (Eq.cong (_* z) (*-comm x y)) (*-assoc y x z))

  fac+ : ∀ s a b → s * a + s * b ≡ s * (a + b)
  fac+ s a b = Eq.sym (*-distribˡ-+ s a b)

  fac− : ∀ s a b → s * a + -1# * (s * b) ≡ s * (a + -1# * b)
  fac− s a b =
    Eq.trans (Eq.cong (s * a +_) (swap-left -1# s b)) (Eq.sym (*-distribˡ-+ s a (-1# * b)))

  -- δ as a Boolean test, the arguments the other way round.
  δ-eq : ∀ {k} (u v : Bits k) → δb u v ≡ (if eqB v u then 1# else 0#)
  δ-eq u v = Eq.trans (δb-eqB u v) (Eq.cong (λ b → if b then 1# else 0#) (eqB-sym u v))

  -- The two rows of a two-level Hadamard, on Booleans.
  row+ : ∀ (bi bj : Bool) → (bi ≡ true → bj ≡ false) →
         (if bi then 1# else if bj then 1# else 0#) ≡ (if bi then 1# else 0#) + (if bj then 1# else 0#)
  row+ true  bj    ex with ex Eq.refl
  ... | Eq.refl = Eq.sym (+-identityʳ 1#)
  row+ false true  _ = Eq.sym (+-identityˡ 1#)
  row+ false false _ = Eq.sym (+-identityˡ 0#)

  row− : ∀ (bi bj : Bool) → (bi ≡ true → bj ≡ false) →
         (if bi then 1# else if bj then -1# else 0#) ≡
         (if bi then 1# else 0#) + -1# * (if bj then 1# else 0#)
  row− true  bj    ex with ex Eq.refl
  ... | Eq.refl = Eq.sym (Eq.trans (Eq.cong (1# +_) (*-zeroʳ -1#)) (+-identityʳ 1#))
  row− false true  _ = Eq.sym (Eq.trans (+-identityˡ _) (*-identityʳ -1#))
  row− false false _ = Eq.sym (Eq.trans (+-identityˡ _) (*-zeroʳ -1#))

  -- δ through an insertion at the same wire.
  δb-insert : ∀ {k} i a b (u w : Bits k) → δb (insertℕ i a u) (insertℕ i b w) ≡ δ₁ a b * δb u w
  δb-insert zero    a b u       w       = δb-∷ a b u w
  δb-insert (suc i) a b []      []      = δb-∷ a b [] []
  δb-insert (suc i) a b (c ∷ u) (d ∷ w) = begin
    δb (c ∷ insertℕ i a u) (d ∷ insertℕ i b w)
      ≡⟨ δb-∷ c d (insertℕ i a u) (insertℕ i b w) ⟩
    δ₁ c d * δb (insertℕ i a u) (insertℕ i b w)
      ≡⟨ Eq.cong (δ₁ c d *_) (δb-insert i a b u w) ⟩
    δ₁ c d * (δ₁ a b * δb u w)
      ≡⟨ swap-left (δ₁ c d) (δ₁ a b) (δb u w) ⟩
    δ₁ a b * (δ₁ c d * δb u w)
      ≡⟨ Eq.cong (δ₁ a b *_) (Eq.sym (δb-∷ c d u w)) ⟩
    δ₁ a b * δb (c ∷ u) (d ∷ w) ∎
    where open Eq.≡-Reasoning

  -- The enumeration of all bitstrings is not empty.
  nonempty : ∀ {k} (c : Bits k) → allBits k ≢ []
  nonempty c e = true≢false (Eq.sym (Eq.subst (λ l → c ∈ᵇ l ≡ true) e (∈-allBits c)))

module _ {m : ℕ} where
  private
    n : ℕ
    n = ₃₊ m
    idx : Bits n → Fin (2 ^ℕ n)
    idx = index n

  ----------------------------------------------------------------------
  -- The Hadamard letter

  private
    -- The wrapper hh is the letter when the indices differ.
    hh-≢ : ∀ a b c d (ab : a ≢ b) (cd : c ≢ d) → hh {n} a b c d ≡ [ HH a b c d ab cd ]ʷ
    hh-≢ a b c d ab cd with a FP.≟ b | c FP.≟ d
    ... | no _   | no _   = Eq.refl
    ... | yes e  | _      = ⊥-elim (ab e)
    ... | no _   | yes e  = ⊥-elim (cd e)

    hadOp-idx : ∀ s s′ → hadOp (code n (idx s)) (code n (idx s′)) ≐ hadOp s s′
    hadOp-idx s s′ =
      Eq.subst₂ (λ v w → hadOp v w ≐ hadOp s s′)
        (Eq.sym (code-index n s)) (Eq.sym (code-index n s′)) (≐-refl (hadOp s s′))

    -- The reading of the letter on two pairs of basis vectors.
    hh-M : ∀ s₀ s₁ s₂ s₃ → s₀ ≢ s₁ → s₂ ≢ s₃ →
           proj₂ ⟦ hh {n = n} (idx s₀) (idx s₁) (idx s₂) (idx s₃) ⟧Y ≐ (hadOp s₀ s₁ ⊙ hadOp s₂ s₃)
    hh-M s₀ s₁ s₂ s₃ d₀ d₂ =
      Eq.subst (λ w → proj₂ ⟦ w ⟧Y ≐ (hadOp s₀ s₁ ⊙ hadOp s₂ s₃))
        (Eq.sym (hh-≢ _ _ _ _ (λ e → d₀ (index-injective n e)) (λ e → d₂ (index-injective n e))))
        (⊙-cong (hadOp-idx s₀ s₁) (hadOp-idx s₂ s₃))

    hh-ℓ : ∀ s₀ s₁ s₂ s₃ → s₀ ≢ s₁ → s₂ ≢ s₃ →
           proj₁ ⟦ hh {n = n} (idx s₀) (idx s₁) (idx s₂) (idx s₃) ⟧Y ≡ 2
    hh-ℓ s₀ s₁ s₂ s₃ d₀ d₂ =
      Eq.cong (λ w → proj₁ ⟦ w ⟧Y)
        (hh-≢ _ _ _ _ (λ e → d₀ (index-injective n e)) (λ e → d₂ (index-injective n e)))

  ----------------------------------------------------------------------
  -- The invariant

  -- On the covered vectors, √2^f times the Hadamard of wire p; on the
  -- others, √2^(f + 1) times the identity.
  part : ℕ → (Bits n → Bool) → ℕ → Op n
  part p cov f x y = if cov x then √2^ f * hadWire p x y else √2^ (suc f) * δb x y

  private
    part-cong : ∀ p {cov cov′} f → (∀ x → cov x ≡ cov′ x) → part p cov f ≐ part p cov′ f
    part-cong p f e x y =
      Eq.cong (λ b → if b then √2^ f * hadWire p x y else √2^ (suc f) * δb x y) (e x)

    part-true : ∀ p cov f x y → cov x ≡ true → part p cov f x y ≡ √2^ f * hadWire p x y
    part-true p cov f x y e = if-true (√2^ f * hadWire p x y) (√2^ (suc f) * δb x y) e

    part-false : ∀ p cov f x y → cov x ≡ false → part p cov f x y ≡ √2^ (suc f) * δb x y
    part-false p cov f x y e = if-false (√2^ f * hadWire p x y) (√2^ (suc f) * δb x y) e

  ----------------------------------------------------------------------
  -- One two-level Hadamard, on a pair of vectors differing at wire p

  private
    -- i has bit p clear and j has it set, the other bits agreeing.
    module Pair (p : ℕ) (q : p < n) (i j : Bits n)
                (rem : removeℕ p i ≡ removeℕ p j)
                (li : lookupℕ p i ≡ false) (lj : lookupℕ p j ≡ true) where

      private
        p≤ : p ≤ ₂₊ m
        p≤ = ≤-pred q

        i≢j : i ≢ j
        i≢j e = true≢false (Eq.trans (Eq.sym lj) (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym e)) li))

        j≢i : j ≢ i
        j≢i e = i≢j (Eq.sym e)

        -- A vector agreeing with i off wire p is i or j.
        in-pair : ∀ y → eqB (removeℕ p i) (removeℕ p y) ≡ true → (y ≡ i) ⊎ (y ≡ j)
        in-pair y e = bool-cases (lookupℕ p y)
          (λ ly → inj₂ (Eq.trans (Eq.sym (insert-lookup-remove p y p≤))
                    (Eq.trans (Eq.cong₂ (insertℕ p) ly (Eq.sym (eqB-sound _ _ e)))
                      (Eq.trans (Eq.cong₂ (insertℕ p) (Eq.sym lj) rem) (insert-lookup-remove p j p≤)))))
          (λ ly → inj₁ (Eq.trans (Eq.sym (insert-lookup-remove p y p≤))
                    (Eq.trans (Eq.cong₂ (insertℕ p) ly (Eq.sym (eqB-sound _ _ e)))
                      (Eq.trans (Eq.cong₂ (insertℕ p) (Eq.sym li) Eq.refl) (insert-lookup-remove p i p≤)))))

        -- Off the pair, a vector is neither i nor j.
        off-pair : ∀ y → eqB (removeℕ p i) (removeℕ p y) ≡ false → eqB y i ≡ false × eqB y j ≡ false
        off-pair y e =
          eqB-false y i (λ yi → true≢false
            (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ v → eqB (removeℕ p i) (removeℕ p v)) yi) (eqB-refl (removeℕ p i)))) e)) ,
          eqB-false y j (λ yj → true≢false
            (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ v → eqB (removeℕ p i) (removeℕ p v)) yj)
                                        (Eq.trans (Eq.cong (λ v → eqB v (removeℕ p j)) rem) (eqB-refl (removeℕ p j))))) e))

        excl : ∀ z → eqB z i ≡ true → eqB z j ≡ false
        excl z e = eqB-false z j (λ zj → i≢j (Eq.trans (Eq.sym (eqB-sound z i e)) zj))

        -- The rows of the two-level Hadamard.
        hadOp-i : ∀ z → hadOp i j i z ≡ δb i z + δb j z
        hadOp-i z =
          Eq.trans (if-true _ _ (eqB-refl i))
            (Eq.trans (row+ (eqB z i) (eqB z j) (excl z))
                      (Eq.sym (Eq.cong₂ _+_ (δ-eq i z) (δ-eq j z))))

        hadOp-j : ∀ z → hadOp i j j z ≡ δb i z + -1# * δb j z
        hadOp-j z =
          Eq.trans (if-false _ _ (eqB-false j i j≢i))
            (Eq.trans (if-true _ _ (eqB-refl j))
              (Eq.trans (row− (eqB z i) (eqB z j) (excl z))
                        (Eq.sym (Eq.cong₂ (λ u v → u + -1# * v) (δ-eq i z) (δ-eq j z)))))

        hadOp-other : ∀ x z → eqB x i ≡ false → eqB x j ≡ false → hadOp i j x z ≡ √2 * δb x z
        hadOp-other x z xi xj = Eq.trans (if-false _ _ xi) (if-false _ _ xj)

        -- δ on the pair.
        δ-at : ∀ y → y ≡ i → δb i y ≡ 1# × δb j y ≡ 0#
        δ-at y yi = Eq.trans (δ-eq i y) (if-true 1# 0# (eqB-complete y i yi)) ,
                    Eq.trans (δ-eq j y) (if-false 1# 0# (eqB-false y j (λ yj → i≢j (Eq.trans (Eq.sym yi) yj))))

        δ-at′ : ∀ y → y ≡ j → δb i y ≡ 0# × δb j y ≡ 1#
        δ-at′ y yj = Eq.trans (δ-eq i y) (if-false 1# 0# (eqB-false y i (λ yi → j≢i (Eq.trans (Eq.sym yj) yi)))) ,
                     Eq.trans (δ-eq j y) (if-true 1# 0# (eqB-complete y j yj))

        δ-off : ∀ y → eqB (removeℕ p i) (removeℕ p y) ≡ false → δb i y ≡ 0# × δb j y ≡ 0#
        δ-off y e = let (yi , yj) = off-pair y e in
          Eq.trans (δ-eq i y) (if-false 1# 0# yi) , Eq.trans (δ-eq j y) (if-false 1# 0# yj)

        -- The Hadamard of wire p on the pair.
        hadWire-i : ∀ y → hadWire p i y ≡ δb i y + δb j y
        hadWire-i y = bool-cases (eqB (removeℕ p i) (removeℕ p y)) on off
          where
          off : eqB (removeℕ p i) (removeℕ p y) ≡ false → hadWire p i y ≡ δb i y + δb j y
          off e = let (di , dj) = δ-off y e in
            Eq.trans (if-false (hval (lookupℕ p i) (lookupℕ p y)) 0# e)
              (Eq.sym (Eq.trans (Eq.cong₂ _+_ di dj) (+-identityˡ 0#)))
          on : eqB (removeℕ p i) (removeℕ p y) ≡ true → hadWire p i y ≡ δb i y + δb j y
          on e with in-pair y e
          ... | inj₁ yi = let (di , dj) = δ-at y yi in
            Eq.trans (if-true (hval (lookupℕ p i) (lookupℕ p y)) 0# e)
              (Eq.trans (Eq.cong₂ hval li (Eq.trans (Eq.cong (lookupℕ p) yi) li))
                (Eq.sym (Eq.trans (Eq.cong₂ _+_ di dj) (+-identityʳ 1#))))
          ... | inj₂ yj = let (di , dj) = δ-at′ y yj in
            Eq.trans (if-true (hval (lookupℕ p i) (lookupℕ p y)) 0# e)
              (Eq.trans (Eq.cong₂ hval li (Eq.trans (Eq.cong (lookupℕ p) yj) lj))
                (Eq.sym (Eq.trans (Eq.cong₂ _+_ di dj) (+-identityˡ 1#))))

        hadWire-j : ∀ y → hadWire p j y ≡ δb i y + -1# * δb j y
        hadWire-j y = bool-cases (eqB (removeℕ p i) (removeℕ p y)) on off
          where
          rem-j : eqB (removeℕ p j) (removeℕ p y) ≡ eqB (removeℕ p i) (removeℕ p y)
          rem-j = Eq.cong (λ v → eqB v (removeℕ p y)) (Eq.sym rem)
          off : eqB (removeℕ p i) (removeℕ p y) ≡ false → hadWire p j y ≡ δb i y + -1# * δb j y
          off e = let (di , dj) = δ-off y e in
            Eq.trans (if-false (hval (lookupℕ p j) (lookupℕ p y)) 0# (Eq.trans rem-j e))
              (Eq.sym (Eq.trans (Eq.cong₂ (λ u v → u + -1# * v) di dj)
                        (Eq.trans (Eq.cong (0# +_) (*-zeroʳ -1#)) (+-identityˡ 0#))))
          on : eqB (removeℕ p i) (removeℕ p y) ≡ true → hadWire p j y ≡ δb i y + -1# * δb j y
          on e with in-pair y e
          ... | inj₁ yi = let (di , dj) = δ-at y yi in
            Eq.trans (if-true (hval (lookupℕ p j) (lookupℕ p y)) 0# (Eq.trans rem-j e))
              (Eq.trans (Eq.cong₂ hval lj (Eq.trans (Eq.cong (lookupℕ p) yi) li))
                (Eq.sym (Eq.trans (Eq.cong₂ (λ u v → u + -1# * v) di dj)
                          (Eq.trans (Eq.cong (1# +_) (*-zeroʳ -1#)) (+-identityʳ 1#)))))
          ... | inj₂ yj = let (di , dj) = δ-at′ y yj in
            Eq.trans (if-true (hval (lookupℕ p j) (lookupℕ p y)) 0# (Eq.trans rem-j e))
              (Eq.trans (Eq.cong₂ hval lj (Eq.trans (Eq.cong (lookupℕ p) yj) lj))
                (Eq.sym (Eq.trans (Eq.cong₂ (λ u v → u + -1# * v) di dj)
                          (Eq.trans (Eq.cong (0# +_) (*-identityʳ -1#)) (+-identityˡ -1#)))))

      -- The letter alone: the first step, from the identity.
      first : ∀ (cov : Bits n → Bool) → (∀ x → cov x ≡ false) →
              hadOp i j ≐ part p (λ x → cov x ∨ eqB x i ∨ eqB x j) 0
      first cov c₀ x y = bool-cases (eqB x i)
        (λ xi → Eq.subst (λ v → hadOp i j v y ≡ part p cov′ 0 v y) (Eq.sym (eqB-sound x i xi)) row-i)
        (λ xi → bool-cases (eqB x j)
          (λ xj → Eq.subst (λ v → hadOp i j v y ≡ part p cov′ 0 v y) (Eq.sym (eqB-sound x j xj)) row-j)
          (λ xj → row-other xi xj))
        where
        cov′ : Bits n → Bool
        cov′ x = cov x ∨ eqB x i ∨ eqB x j
        row-i : hadOp i j i y ≡ part p cov′ 0 i y
        row-i = Eq.trans (hadOp-i y)
          (Eq.trans (Eq.sym (hadWire-i y))
            (Eq.trans (Eq.sym (*-identityˡ (hadWire p i y)))
              (Eq.sym (part-true p cov′ 0 i y (Eq.cong₂ _∨_ (c₀ i) (Eq.cong (_∨ eqB i j) (eqB-refl i)))))))
        row-j : hadOp i j j y ≡ part p cov′ 0 j y
        row-j = Eq.trans (hadOp-j y)
          (Eq.trans (Eq.sym (hadWire-j y))
            (Eq.trans (Eq.sym (*-identityˡ (hadWire p j y)))
              (Eq.sym (part-true p cov′ 0 j y (Eq.cong₂ _∨_ (c₀ j) (Eq.cong₂ _∨_ (eqB-false j i j≢i) (eqB-refl j)))))))
        row-other : eqB x i ≡ false → eqB x j ≡ false → hadOp i j x y ≡ part p cov′ 0 x y
        row-other xi xj = Eq.trans (hadOp-other x y xi xj)
          (Eq.trans (Eq.cong (_* δb x y) (Eq.sym √2^1))
            (Eq.sym (part-false p cov′ 0 x y
              (Eq.trans (Eq.cong (cov x ∨_) (Eq.cong₂ _∨_ xi xj)) (Eq.trans (∨-identityʳ (cov x)) (c₀ x))))))

      -- The letter on the invariant: one step.
      step : ∀ (cov : Bits n → Bool) f → cov i ≡ false → cov j ≡ false →
             (hadOp i j ⊙ part p cov f) ≐ part p (λ x → cov x ∨ eqB x i ∨ eqB x j) (suc f)
      step cov f ci cj x y = bool-cases (eqB x i)
        (λ xi → Eq.subst (λ v → Σb (λ z → hadOp i j v z * M z y) ≡ part p cov′ (suc f) v y)
                  (Eq.sym (eqB-sound x i xi)) row-i)
        (λ xi → bool-cases (eqB x j)
          (λ xj → Eq.subst (λ v → Σb (λ z → hadOp i j v z * M z y) ≡ part p cov′ (suc f) v y)
                    (Eq.sym (eqB-sound x j xj)) row-j)
          (λ xj → row-other xi xj))
        where
        open Eq.≡-Reasoning
        M : Op n
        M = part p cov f
        cov′ : Bits n → Bool
        cov′ x = cov x ∨ eqB x i ∨ eqB x j
        row-i : Σb (λ z → hadOp i j i z * M z y) ≡ part p cov′ (suc f) i y
        row-i = begin
          Σb (λ z → hadOp i j i z * M z y)
            ≡⟨ Σ-cong (λ z → Eq.cong (_* M z y) (hadOp-i z)) ⟩
          Σb (λ z → (δb i z + δb j z) * M z y)
            ≡⟨ Σ-cong (λ z → *-distribʳ-+ (M z y) (δb i z) (δb j z)) ⟩
          Σb (λ z → δb i z * M z y + δb j z * M z y)
            ≡⟨ Σ-add (λ z → δb i z * M z y) (λ z → δb j z * M z y) ⟩
          Σb (λ z → δb i z * M z y) + Σb (λ z → δb j z * M z y)
            ≡⟨ Eq.cong₂ _+_ (Σ-δˡ i (λ z → M z y)) (Σ-δˡ j (λ z → M z y)) ⟩
          M i y + M j y
            ≡⟨ Eq.cong₂ _+_ (part-false p cov f i y ci) (part-false p cov f j y cj) ⟩
          √2^ (suc f) * δb i y + √2^ (suc f) * δb j y
            ≡⟨ fac+ (√2^ (suc f)) (δb i y) (δb j y) ⟩
          √2^ (suc f) * (δb i y + δb j y)
            ≡⟨ Eq.cong (√2^ (suc f) *_) (Eq.sym (hadWire-i y)) ⟩
          √2^ (suc f) * hadWire p i y
            ≡⟨ Eq.sym (part-true p cov′ (suc f) i y (Eq.cong₂ _∨_ ci (Eq.cong (_∨ eqB i j) (eqB-refl i)))) ⟩
          part p cov′ (suc f) i y ∎
        row-j : Σb (λ z → hadOp i j j z * M z y) ≡ part p cov′ (suc f) j y
        row-j = begin
          Σb (λ z → hadOp i j j z * M z y)
            ≡⟨ Σ-cong (λ z → Eq.cong (_* M z y) (hadOp-j z)) ⟩
          Σb (λ z → (δb i z + -1# * δb j z) * M z y)
            ≡⟨ Σ-cong (λ z → *-distribʳ-+ (M z y) (δb i z) (-1# * δb j z)) ⟩
          Σb (λ z → δb i z * M z y + (-1# * δb j z) * M z y)
            ≡⟨ Σ-cong (λ z → Eq.cong (δb i z * M z y +_) (*-assoc -1# (δb j z) (M z y))) ⟩
          Σb (λ z → δb i z * M z y + -1# * (δb j z * M z y))
            ≡⟨ Σ-add (λ z → δb i z * M z y) (λ z → -1# * (δb j z * M z y)) ⟩
          Σb (λ z → δb i z * M z y) + Σb (λ z → -1# * (δb j z * M z y))
            ≡⟨ Eq.cong₂ _+_ (Σ-δˡ i (λ z → M z y))
                 (Eq.trans (Σ-scaleˡ -1# (λ z → δb j z * M z y)) (Eq.cong (-1# *_) (Σ-δˡ j (λ z → M z y)))) ⟩
          M i y + -1# * M j y
            ≡⟨ Eq.cong₂ (λ u v → u + -1# * v) (part-false p cov f i y ci) (part-false p cov f j y cj) ⟩
          √2^ (suc f) * δb i y + -1# * (√2^ (suc f) * δb j y)
            ≡⟨ fac− (√2^ (suc f)) (δb i y) (δb j y) ⟩
          √2^ (suc f) * (δb i y + -1# * δb j y)
            ≡⟨ Eq.cong (√2^ (suc f) *_) (Eq.sym (hadWire-j y)) ⟩
          √2^ (suc f) * hadWire p j y
            ≡⟨ Eq.sym (part-true p cov′ (suc f) j y (Eq.cong₂ _∨_ cj (Eq.cong₂ _∨_ (eqB-false j i j≢i) (eqB-refl j)))) ⟩
          part p cov′ (suc f) j y ∎
        row-other : eqB x i ≡ false → eqB x j ≡ false →
                    Σb (λ z → hadOp i j x z * M z y) ≡ part p cov′ (suc f) x y
        row-other xi xj = begin
          Σb (λ z → hadOp i j x z * M z y)
            ≡⟨ Σ-cong (λ z → Eq.cong (_* M z y) (hadOp-other x z xi xj)) ⟩
          Σb (λ z → (√2 * δb x z) * M z y)
            ≡⟨ Σ-cong (λ z → *-assoc √2 (δb x z) (M z y)) ⟩
          Σb (λ z → √2 * (δb x z * M z y))
            ≡⟨ Σ-scaleˡ √2 (λ z → δb x z * M z y) ⟩
          √2 * Σb (λ z → δb x z * M z y)
            ≡⟨ Eq.cong (√2 *_) (Σ-δˡ x (λ z → M z y)) ⟩
          √2 * M x y
            ≡⟨ lift ⟩
          part p cov′ (suc f) x y ∎
          where
          c′x : cov′ x ≡ cov x
          c′x = Eq.trans (Eq.cong (cov x ∨_) (Eq.cong₂ _∨_ xi xj)) (∨-identityʳ (cov x))
          lift : √2 * M x y ≡ part p cov′ (suc f) x y
          lift = bool-cases (cov x)
            (λ cx → begin
               √2 * M x y
                 ≡⟨ Eq.cong (√2 *_) (part-true p cov f x y cx) ⟩
               √2 * (√2^ f * hadWire p x y)
                 ≡⟨ Eq.sym (*-assoc √2 (√2^ f) (hadWire p x y)) ⟩
               (√2 * √2^ f) * hadWire p x y
                 ≡⟨ Eq.cong (_* hadWire p x y) (Eq.sym (√2^-suc f)) ⟩
               √2^ (suc f) * hadWire p x y
                 ≡⟨ Eq.sym (part-true p cov′ (suc f) x y (Eq.trans c′x cx)) ⟩
               part p cov′ (suc f) x y ∎)
            (λ cx → begin
               √2 * M x y
                 ≡⟨ Eq.cong (√2 *_) (part-false p cov f x y cx) ⟩
               √2 * (√2^ (suc f) * δb x y)
                 ≡⟨ Eq.sym (*-assoc √2 (√2^ (suc f)) (δb x y)) ⟩
               (√2 * √2^ (suc f)) * δb x y
                 ≡⟨ Eq.cong (_* δb x y) (Eq.sym (√2^-suc (suc f))) ⟩
               √2^ (suc (suc f)) * δb x y
                 ≡⟨ Eq.sym (part-false p cov′ (suc f) x y (Eq.trans c′x cx)) ⟩
               part p cov′ (suc f) x y ∎)

  ----------------------------------------------------------------------
  -- The product over all contexts
  --
  -- A gate on wire p, whose letters are on the vectors v c b g (context
  -- c, pairing bit b, gate bit g), fires on the vectors satisfying a
  -- control condition ctl (always, for H; the control bit, for CH);
  -- ctx and pr read the context and the pairing bit off a vector.

  private
    module Encode (k : ℕ) (p : ℕ) (q : p < n)
                  (v : Bits k → Bool → Bool → Bits n)
                  (ctl : Bits n → Bool) (ctx : Bits n → Bits k) (pr : Bits n → Bool)
                  (rem-v : ∀ c b g g′ → removeℕ p (v c b g) ≡ removeℕ p (v c b g′))
                  (bit-v : ∀ c b g → lookupℕ p (v c b g) ≡ g)
                  (pr-v  : ∀ c b g → pr (v c b g) ≡ b)
                  (ctx-v : ∀ c b g → ctx (v c b g) ≡ c)
                  (ctl-v : ∀ c b g → ctl (v c b g) ≡ true)
                  (v-ctx : ∀ x → ctl x ≡ true → x ≡ v (ctx x) (pr x) (lookupℕ p x))
                  (T : Op n)
                  (T-ctl : ∀ x y → ctl x ≡ true → T x y ≡ hadWire p x y)
                  (T-off : ∀ x y → ctl x ≡ false → T x y ≡ √2 * δb x y)
      where

      -- The word, the letter of a context and the cover of a list of
      -- contexts.
      word : List (Bits k) → Word (GenP n)
      word cs = ∏ cs (λ c → hh {n = n} (idx (v c false false)) (idx (v c false true))
                               (idx (v c true false))  (idx (v c true true)))

      L : Bits k → Op n
      L c = hadOp (v c false false) (v c false true) ⊙ hadOp (v c true false) (v c true true)

      cov : List (Bits k) → Bits n → Bool
      cov cs x = ctl x ∧ (ctx x ∈ᵇ cs)

      len2 : List (Bits k) → ℕ
      len2 = foldr (λ _ f → suc (suc f)) 0

      partL : List (Bits k) → Op n
      partL []       = Idₒ
      partL (c ∷ cs) = part p (cov (c ∷ cs)) (suc (len2 cs))

      private
        -- The four vectors of a context differ in their pairing bit or
        -- in their gate bit.
        v-pr : ∀ c g g′ → eqB (v c false g) (v c true g′) ≡ false
        v-pr c g g′ = eqB-false _ _ (λ e → true≢false
          (Eq.trans (Eq.sym (pr-v c true g′)) (Eq.trans (Eq.cong pr (Eq.sym e)) (pr-v c false g))))

        v-bit : ∀ c b → v c b false ≢ v c b true
        v-bit c b e = true≢false
          (Eq.trans (Eq.sym (bit-v c b true)) (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym e)) (bit-v c b false)))

        module P₀ (c : Bits k) =
          Pair p q (v c false false) (v c false true) (rem-v c false false true) (bit-v c false false) (bit-v c false true)
        module P₁ (c : Bits k) =
          Pair p q (v c true false) (v c true true) (rem-v c true false true) (bit-v c true false) (bit-v c true true)

        -- The cover after the two pairs of a context, and its
        -- canonical form.
        cov₂ : List (Bits k) → Bits k → Bits n → Bool
        cov₂ cs c x = (cov cs x ∨ eqB x (v c true false) ∨ eqB x (v c true true)) ∨
                      eqB x (v c false false) ∨ eqB x (v c false true)

        cov-∷ : ∀ cs c x → cov₂ cs c x ≡ cov (c ∷ cs) x
        cov-∷ cs c x = bool-cases (ctl x) on off
          where
          off : ctl x ≡ false → cov₂ cs c x ≡ cov (c ∷ cs) x
          off cx = Eq.trans lhs (Eq.sym (Eq.cong (_∧ (ctx x ∈ᵇ (c ∷ cs))) cx))
            where
            no-v : ∀ b g → eqB x (v c b g) ≡ false
            no-v b g = eqB-false x _ (λ e → true≢false
              (Eq.trans (Eq.sym (ctl-v c b g)) (Eq.trans (Eq.cong ctl (Eq.sym e)) cx)))
            lhs : cov₂ cs c x ≡ false
            lhs = Eq.cong₂ _∨_
                    (Eq.cong₂ _∨_ (Eq.cong (_∧ (ctx x ∈ᵇ cs)) cx) (Eq.cong₂ _∨_ (no-v true false) (no-v true true)))
                    (Eq.cong₂ _∨_ (no-v false false) (no-v false true))
          on : ctl x ≡ true → cov₂ cs c x ≡ cov (c ∷ cs) x
          on cx = bool-cases (eqB (ctx x) c) here there
            where
            -- The context of x is c: x is one of the four vectors.
            here : eqB (ctx x) c ≡ true → cov₂ cs c x ≡ cov (c ∷ cs) x
            here ec = Eq.trans lhs (Eq.sym (Eq.trans (Eq.cong (_∧ (eqB (ctx x) c ∨ (ctx x ∈ᵇ cs))) cx) rhs))
              where
              x≡ : x ≡ v c (pr x) (lookupℕ p x)
              x≡ = Eq.trans (v-ctx x cx) (Eq.cong (λ c′ → v c′ (pr x) (lookupℕ p x)) (eqB-sound (ctx x) c ec))
              at : ∀ b g → pr x ≡ b → lookupℕ p x ≡ g → eqB x (v c b g) ≡ true
              at b g pb lg = eqB-complete x _ (Eq.trans x≡ (Eq.cong₂ (v c) pb lg))
              rhs : (eqB (ctx x) c ∨ (ctx x ∈ᵇ cs)) ≡ true
              rhs = Eq.cong (_∨ (ctx x ∈ᵇ cs)) ec
              A B₁ C₁ B₀ C₀ : Bool
              A  = cov cs x
              B₁ = eqB x (v c true false)
              C₁ = eqB x (v c true true)
              B₀ = eqB x (v c false false)
              C₀ = eqB x (v c false true)
              lhs : cov₂ cs c x ≡ true
              lhs = bool-cases (pr x)
                (λ pb → bool-cases (lookupℕ p x)
                  (λ lg → or2 A B₁ C₁ B₀ C₀ (at true true pb lg))
                  (λ lg → or1 A B₁ C₁ B₀ C₀ (at true false pb lg)))
                (λ pb → bool-cases (lookupℕ p x)
                  (λ lg → or4 A B₁ C₁ B₀ C₀ (at false true pb lg))
                  (λ lg → or3 A B₁ C₁ B₀ C₀ (at false false pb lg)))
            -- The context of x is not c: x is none of the four.
            there : eqB (ctx x) c ≡ false → cov₂ cs c x ≡ cov (c ∷ cs) x
            there ec =
              Eq.trans lhs
                (Eq.trans (Eq.cong (_∧ (ctx x ∈ᵇ cs)) cx)
                  (Eq.sym (Eq.cong₂ _∧_ cx (Eq.cong (_∨ (ctx x ∈ᵇ cs)) ec))))
              where
              no-v : ∀ b g → eqB x (v c b g) ≡ false
              no-v b g = eqB-false x _ (λ e → true≢false
                (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ y → eqB (ctx y) c) e)
                                            (Eq.trans (Eq.cong (λ y → eqB y c) (ctx-v c b g)) (eqB-refl c))))
                          ec))
              lhs : cov₂ cs c x ≡ cov cs x
              lhs = Eq.trans
                (Eq.cong₂ _∨_ (Eq.cong (cov cs x ∨_) (Eq.cong₂ _∨_ (no-v true false) (no-v true true)))
                              (Eq.cong₂ _∨_ (no-v false false) (no-v false true)))
                (Eq.trans (∨-identityʳ (cov cs x ∨ false)) (∨-identityʳ (cov cs x)))

        -- A context not yet processed: its vectors are uncovered.
        unc : ∀ cs c → c ∈ᵇ cs ≡ false → ∀ b g → cov cs (v c b g) ≡ false
        unc cs c nc b g = Eq.trans (Eq.cong₂ _∧_ (ctl-v c b g) (Eq.cong (_∈ᵇ cs) (ctx-v c b g))) nc

        -- The letter of a context on the invariant: two steps.
        ctx-step : ∀ cs c → c ∈ᵇ cs ≡ false → ∀ f →
                   (L c ⊙ part p (cov cs) f) ≐ part p (cov₂ cs c) (suc (suc f))
        ctx-step cs c nc f =
          ≐-trans (⊙-assoc (hadOp (v c false false) (v c false true)) (hadOp (v c true false) (v c true true)) (part p (cov cs) f))
            (≐-trans (⊙-cong {N' = part p cov₁ (suc f)} (≐-refl (hadOp (v c false false) (v c false true)))
                             (P₁.step c (cov cs) f (unc cs c nc true false) (unc cs c nc true true)))
                     (P₀.step c cov₁ (suc f)
                        (Eq.cong₂ _∨_ (unc cs c nc false false) (Eq.cong₂ _∨_ (v-pr c false false) (v-pr c false true)))
                        (Eq.cong₂ _∨_ (unc cs c nc false true)  (Eq.cong₂ _∨_ (v-pr c true false)  (v-pr c true true)))))
          where
          cov₁ : Bits n → Bool
          cov₁ x = cov cs x ∨ eqB x (v c true false) ∨ eqB x (v c true true)

        -- The first context, from the identity.
        ctx-first : ∀ c → (L c ⊙ Idₒ) ≐ part p (cov₂ [] c) 1
        ctx-first c =
          ≐-trans (⊙-identityʳ (L c))
            (≐-trans (⊙-cong {N' = part p cov₁ 0} (≐-refl (hadOp (v c false false) (v c false true)))
                             (P₁.first c (cov []) (λ x → ∧-zeroʳ (ctl x))))
                     (P₀.step c cov₁ 0
                        (Eq.cong₂ _∨_ (∧-zeroʳ (ctl (v c false false))) (Eq.cong₂ _∨_ (v-pr c false false) (v-pr c false true)))
                        (Eq.cong₂ _∨_ (∧-zeroʳ (ctl (v c false true)))  (Eq.cong₂ _∨_ (v-pr c true false)  (v-pr c true true)))))
          where
          cov₁ : Bits n → Bool
          cov₁ x = cov [] x ∨ eqB x (v c true false) ∨ eqB x (v c true true)

        -- The product of the letters over a list of distinct contexts.
        fold : ∀ cs → Nodup cs → foldr (λ c M → L c ⊙ M) Idₒ cs ≐ partL cs
        fold []            _         = ≐-refl Idₒ
        fold (c ∷ [])      _         = ≐-trans (ctx-first c) (part-cong p 1 (cov-∷ [] c))
        fold (c ∷ c′ ∷ cs) (nc , nd) =
          ≐-trans (⊙-cong (≐-refl (L c)) (fold (c′ ∷ cs) nd))
            (≐-trans (ctx-step (c′ ∷ cs) c nc (suc (len2 cs)))
                     (part-cong p (suc (suc (suc (len2 cs)))) (cov-∷ (c′ ∷ cs) c)))

        -- With every context covered, the invariant is the gate.
        final : ∀ cs → (∀ x → ctl x ≡ true → ctx x ∈ᵇ cs ≡ true) → cs ≢ [] →
                (√2 · partL cs) ≐ (√2^ (len2 cs) · T)
        final []       _   ne = ⊥-elim (ne Eq.refl)
        final (c ∷ cs) all _  x y = bool-cases (ctl x)
          (λ cx → begin
             √2 * part p (cov (c ∷ cs)) (suc (len2 cs)) x y
               ≡⟨ Eq.cong (√2 *_) (part-true p (cov (c ∷ cs)) (suc (len2 cs)) x y (Eq.cong₂ _∧_ cx (all x cx))) ⟩
             √2 * (√2^ (suc (len2 cs)) * hadWire p x y)
               ≡⟨ Eq.sym (*-assoc √2 (√2^ (suc (len2 cs))) (hadWire p x y)) ⟩
             (√2 * √2^ (suc (len2 cs))) * hadWire p x y
               ≡⟨ Eq.cong₂ _*_ (Eq.sym (√2^-suc (suc (len2 cs)))) (Eq.sym (T-ctl x y cx)) ⟩
             √2^ (suc (suc (len2 cs))) * T x y ∎)
          (λ cx → begin
             √2 * part p (cov (c ∷ cs)) (suc (len2 cs)) x y
               ≡⟨ Eq.cong (√2 *_) (part-false p (cov (c ∷ cs)) (suc (len2 cs)) x y (Eq.cong (_∧ (ctx x ∈ᵇ (c ∷ cs))) cx)) ⟩
             √2 * (√2^ (suc (suc (len2 cs))) * δb x y)
               ≡⟨ swap-left √2 (√2^ (suc (suc (len2 cs)))) (δb x y) ⟩
             √2^ (suc (suc (len2 cs))) * (√2 * δb x y)
               ≡⟨ Eq.cong (√2^ (suc (suc (len2 cs))) *_) (Eq.sym (T-off x y cx)) ⟩
             √2^ (suc (suc (len2 cs))) * T x y ∎)
          where open Eq.≡-Reasoning

        -- The reading of the word.
        word-M : ∀ cs → Nodup cs → proj₂ ⟦ word cs ⟧Y ≐ partL cs
        word-M cs nd =
          ≐-trans (∏-M {m = m} cs (λ c → hh (idx (v c false false)) (idx (v c false true)) (idx (v c true false)) (idx (v c true true))))
            (≐-trans (fold-cong cs (λ c → hh-M (v c false false) (v c false true) (v c true false) (v c true true) (v-bit c false) (v-bit c true)))
                     (fold cs nd))

        word-ℓ : ∀ cs → proj₁ ⟦ word cs ⟧Y ≡ len2 cs
        word-ℓ cs =
          Eq.trans (∏-ℓ {m = m} cs (λ c → hh (idx (v c false false)) (idx (v c false true)) (idx (v c true false)) (idx (v c true true))))
                   (sum cs)
          where
          sum : ∀ cs → foldr (λ c f → proj₁ ⟦ hh {n = n} (idx (v c false false)) (idx (v c false true)) (idx (v c true false)) (idx (v c true true)) ⟧Y +ℕ f) 0 cs ≡ len2 cs
          sum []       = Eq.refl
          sum (c ∷ cs) = Eq.cong₂ _+ℕ_ (hh-ℓ (v c false false) (v c false true) (v c true false) (v c true true) (v-bit c false) (v-bit c true)) (sum cs)

      -- The word over every context is the gate.
      sem : ∀ cs → Nodup cs → (∀ x → ctl x ≡ true → ctx x ∈ᵇ cs ≡ true) → cs ≢ [] →
            ⟦ word cs ⟧Y ~ (1 , T)
      sem cs nd all ne =
        ≐-trans (·-cong √2^1 (word-M cs nd))
          (≐-trans (final cs all ne)
                   (·-cong (Eq.cong √2^_ (Eq.sym (word-ℓ cs))) (≐-refl T)))

  ----------------------------------------------------------------------
  -- H on wire p

  private
    -- Removing wire p from the vectors of a context does not see the
    -- gate bit.
    rem-str₁ : ∀ p → p < n → ∀ (c : Bits (₁₊ m)) b g g′ → removeℕ p (str₁ p c b g) ≡ removeℕ p (str₁ p c b g′)
    rem-str₁ zero    _       c b g g′ = Eq.trans (rem₀ g) (Eq.sym (rem₀ g′))
      where
      rem₀ : ∀ g → removeℕ 0 (str₁ 0 c b g) ≡ insertℕ (₁₊ m) b c
      rem₀ g = remove-insert-below (₁₊ m) 0 b (insertℕ 0 g c) z≤n ≤-refl
    rem-str₁ (suc p) (s≤s q) c b g g′ =
      Eq.trans (remove-insert (suc p) g (insertℕ p b c) q) (Eq.sym (remove-insert (suc p) g′ (insertℕ p b c) q))

  E-H-sem : ∀ p → p < n → _~_ {n = n} (⟦_⟧Y {m = m} (E-H {m = m} p)) (1 , hadWire {n = ₂₊ m} p)
  E-H-sem p q =
    H.sem (allBits (₁₊ m)) (allBits-nodup (₁₊ m)) (λ x _ → ∈-allBits (ctx₁ p x)) (nonempty (replicate (₁₊ m) false))
    where
    module H = Encode (₁₊ m) p q (str₁ {m = m} p) (λ _ → true) (ctx₁ {m = m} p) (pr₁ {m = m} p)
                 (rem-str₁ p q) (λ c b g → bit-str₁ {m = m} p c b g q) (λ c b g → pr-str₁ {m = m} p c b g q)
                 (λ c b g → ctx-str₁ {m = m} p c b g q) (λ _ _ _ → Eq.refl) (λ x _ → Eq.sym (str-ctx₁ {m = m} p x q))
                 (hadWire p) (λ _ _ _ → Eq.refl) (λ _ _ e → ⊥-elim (true≢false e))

  ----------------------------------------------------------------------
  -- CH on wires p and p + 1

  private
    rem-str₂ : ∀ p → suc p < n → ∀ (c : Bits m) b u t t′ → removeℕ p (str₂ p c b u t) ≡ removeℕ p (str₂ p c b u t′)
    rem-str₂ zero    _             c b u t t′ = Eq.trans (rem₀ t) (Eq.sym (rem₀ t′))
      where
      rem₀ : ∀ t → removeℕ 0 (str₂ 0 c b u t) ≡ insertℕ (₁₊ m) b (u ∷ c)
      rem₀ t = remove-insert-below (₁₊ m) 0 b (insertℕ 1 u (insertℕ 0 t c)) z≤n ≤-refl
    rem-str₂ (suc p) (s≤s (s≤s q)) c b u t t′ = Eq.trans (rem₁ t) (Eq.sym (rem₁ t′))
      where
      rem₁ : ∀ t → removeℕ (suc p) (str₂ (suc p) c b u t) ≡ insertℕ (suc p) u (insertℕ p b c)
      rem₁ t = Eq.trans (remove-insert-below (suc p) (suc p) u (insertℕ (suc p) t (insertℕ p b c)) ≤-refl q)
                        (Eq.cong (insertℕ (suc p) u) (remove-insert (suc p) t (insertℕ p b c) q))

    -- δ at wire p and off it.
    δb-split : ∀ p (x y : Bits n) → p ≤ ₂₊ m →
               δb x y ≡ (if eqB (removeℕ p x) (removeℕ p y) then δ₁ (lookupℕ p x) (lookupℕ p y) else 0#)
    δb-split p x y p≤ = begin
      δb x y
        ≡⟨ Eq.cong₂ δb (Eq.sym (insert-lookup-remove p x p≤)) (Eq.sym (insert-lookup-remove p y p≤)) ⟩
      δb (insertℕ p (lookupℕ p x) (removeℕ p x)) (insertℕ p (lookupℕ p y) (removeℕ p y))
        ≡⟨ δb-insert p (lookupℕ p x) (lookupℕ p y) (removeℕ p x) (removeℕ p y) ⟩
      δ₁ (lookupℕ p x) (lookupℕ p y) * δb (removeℕ p x) (removeℕ p y)
        ≡⟨ Eq.cong (δ₁ (lookupℕ p x) (lookupℕ p y) *_) (δb-eqB (removeℕ p x) (removeℕ p y)) ⟩
      δ₁ (lookupℕ p x) (lookupℕ p y) * (if eqB (removeℕ p x) (removeℕ p y) then 1# else 0#)
        ≡⟨ *-if (δ₁ (lookupℕ p x) (lookupℕ p y)) (eqB (removeℕ p x) (removeℕ p y)) ⟩
      (if eqB (removeℕ p x) (removeℕ p y) then δ₁ (lookupℕ p x) (lookupℕ p y) else 0#) ∎
      where
      open Eq.≡-Reasoning
      *-if : ∀ d b → d * (if b then 1# else 0#) ≡ (if b then d else 0#)
      *-if d true  = *-identityʳ d
      *-if d false = *-zeroʳ d

    -- The matrix of CH, on the control condition.
    chWire-ctl : ∀ p (x y : Bits n) → lookupℕ (suc p) x ≡ true → chWire p x y ≡ hadWire p x y
    chWire-ctl p x y cx = bool-cases (eqB (removeℕ p x) (removeℕ p y))
      (λ e → Eq.trans (if-true _ 0# e)
               (Eq.trans (if-true (hval (lookupℕ p x) (lookupℕ p y)) (√2 * δ₁ (lookupℕ p x) (lookupℕ p y)) cx)
                         (Eq.sym (if-true (hval (lookupℕ p x) (lookupℕ p y)) 0# e))))
      (λ e → Eq.trans (if-false _ 0# e) (Eq.sym (if-false (hval (lookupℕ p x) (lookupℕ p y)) 0# e)))

    chWire-off : ∀ p (x y : Bits n) → p ≤ ₂₊ m → lookupℕ (suc p) x ≡ false → chWire p x y ≡ √2 * δb x y
    chWire-off p x y p≤ cx = bool-cases (eqB (removeℕ p x) (removeℕ p y))
      (λ e → Eq.trans (if-true _ 0# e)
               (Eq.trans (if-false (hval (lookupℕ p x) (lookupℕ p y)) (√2 * δ₁ (lookupℕ p x) (lookupℕ p y)) cx)
                         (Eq.cong (√2 *_) (Eq.sym (Eq.trans (δb-split p x y p≤) (if-true _ 0# e))))))
      (λ e → Eq.trans (if-false _ 0# e)
               (Eq.sym (Eq.trans (Eq.cong (√2 *_) (Eq.trans (δb-split p x y p≤) (if-false _ 0# e))) (*-zeroʳ √2))))

  E-CH-sem : ∀ p → suc p < n → _~_ {n = n} (⟦_⟧Y {m = m} (E-CH {m = m} p)) (1 , chWire {n = ₂₊ m} p)
  E-CH-sem p q =
    CH.sem (allBits m) (allBits-nodup m) (λ x _ → ∈-allBits (ctx₂ p x)) (nonempty (replicate m false))
    where
    p< : p < n
    p< = ≤-trans (n≤1+n (suc p)) q
    module CH = Encode m p p< (λ c b t → str₂ {m = m} p c b true t) (lookupℕ (suc p)) (ctx₂ {m = m} p) (pr₂ {m = m} p)
                  (λ c b t t′ → rem-str₂ p q c b true t t′) (λ c b t → bit-str₂ {m = m} p c b true t q)
                  (λ c b t → pr-str₂ {m = m} p c b true t q) (λ c b t → ctx-str₂ {m = m} p c b true t q)
                  (λ c b t → ctl-str₂ {m = m} p c b true t q)
                  (λ x cx → Eq.sym (Eq.subst (λ u → str₂ {m = m} p (ctx₂ p x) (pr₂ p x) u (lookupℕ p x) ≡ x) cx (str-ctx₂ {m = m} p x q)))
                  (chWire p) (chWire-ctl p) (λ x y cx → chWire-off p x y (≤-pred p<) cx)
