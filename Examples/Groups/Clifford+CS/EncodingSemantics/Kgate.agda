------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoding preserves the semantics of K
--
-- The letters of E(K on wire p) are the two-level K's on the pairs of
-- basis vectors that differ only at wire p, each pair once.  Their
-- product is computed through an invariant over the contexts
-- processed so far: on the vectors already covered it is K on wire p,
-- on the others the identity, each up to the power of γ the factors so
-- far contribute; one letter on an uncovered pair moves the invariant
-- one step.  A letter whose pair comes reversed in the Gray numbering
-- is spelled (−1)_[a] K_[b,a] (−1)_[b], which reads as the same
-- operator (`rev-K`).
--
-- After Real-Clifford+CH.EncodingSemantics.Hadamard, with one pair
-- per context.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.EncodingSemantics.Kgate (m : ℕ) where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool using (Bool ; true ; false ; _∨_ ; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (_<_ to _<ᶠ_)
open import Data.List using (List ; [] ; _∷_ ; foldr ; length)
open import Data.Nat using (zero ; suc ; _<_ ; _≤_ ; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (replicate)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Data.Fin.Properties as FinP

open import Notations using (₃₊)

open import Examples.Groups.Clifford+CS.Semantics
open import Examples.Groups.Clifford+CS.Semantics.Ring using (+-*-commutativeRing)
open import Algebra.Properties.Ring (CommutativeRing.ring +-*-commutativeRing) using (-1*x≈-x)
open import Examples.Groups.Clifford+CS.Encoding m
open import Examples.Groups.Clifford+CS.BridgeGray n
  using (⟦_⟧Y ; coefℤ ; cK-a ; cK-b ; cK-≢)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Diag
open import Examples.Groups.Clifford+CS.EncodingSemantics.Products n
open import Examples.Groups.Clifford+CS.EncodingSemantics.Letters m
open import Examples.Groups.Clifford+CS.EncodingSemantics.WireForms m using (kWire ; kval ; δb-eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

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

  -- Three rewrites and a closed computation.
  by3 : ∀ {P : 𝔽 → 𝔽 → 𝔽 → Set} {a a′ b b′ c c′ : 𝔽} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → P a′ b′ c′ → P a b c
  by3 Eq.refl Eq.refl Eq.refl h = h

  -- x * (y * z) with x and y exchanged.
  swap-left : ∀ (x y z : 𝔽) → x * (y * z) ≡ y * (x * z)
  swap-left x y z = Eq.trans (Eq.sym (*-assoc x y z)) (Eq.trans (Eq.cong (_* z) (*-comm x y)) (*-assoc y x z))

  fac+ : ∀ (s a b : 𝔽) → s * a + s * b ≡ s * (a + b)
  fac+ s a b = Eq.sym (*-distribˡ-+ s a b)

  fac− : ∀ (s a b : 𝔽) → s * a + -1# * (s * b) ≡ s * (a + -1# * b)
  fac− s a b = Eq.trans (Eq.cong (s * a +_) (swap-left -1# s b)) (fac+ s a (-1# * b))

  -- −1 times.
  -1*x : ∀ v → -1# * v ≡ - v
  -1*x v = -1*x≈-x v

  -- δ, through the Boolean equality (the other way round from δb-eqB).
  δ-eq : ∀ (u v : Bits n) → δb u v ≡ (if eqB v u then 1# else 0#)
  δ-eq u v = Eq.trans (δb-sym u v) (δb-eqB v u)

------------------------------------------------------------------------
-- The K letter on a pair of basis vectors
--
-- γ K on the span of i (the vector where the wire reads 0) and j
-- (where it reads 1), row by row.

kOp : Bits n → Bits n → Op n
kOp i j x y =
  if eqB x i then δb i y + δb j y
  else if eqB x j then δb i y + -1# * δb j y
  else γ * δb x y

private
  kOp-i : ∀ i j z → kOp i j i z ≡ δb i z + δb j z
  kOp-i i j z = if-true _ _ (eqB-refl i)

  kOp-j : ∀ i j z → i ≢ j → kOp i j j z ≡ δb i z + -1# * δb j z
  kOp-j i j z i≢j =
    Eq.trans (if-false _ _ (eqB-false j i (λ e → i≢j (Eq.sym e)))) (if-true _ _ (eqB-refl j))

  kOp-other : ∀ i j x z → eqB x i ≡ false → eqB x j ≡ false → kOp i j x z ≡ γ * δb x z
  kOp-other i j x z xi xj = Eq.trans (if-false _ _ xi) (if-false _ _ xj)

  -- The two-level K_[a,b] read on bit vectors, a < b.
  K-M : ∀ (s s′ : Bits n) .(p : idx s <ᶠ idx s′) →
        proj₂ ⟦ TL.K (idx s) (idx s′) p ⟧Y ≐ kOp s s′
  K-M s s′ p x y = go (idx x FinP.≟ idx s) (idx x FinP.≟ idx s′)
    where
    -- The row of s, and the row of s′, transported to any vector equal
    -- to them.
    at-s : ∀ v → v ≡ s → coefℤ (TL.K-gen (idx s) (idx s′) p) (idx v) (idx y) ≡ kOp s s′ v y
    at-s v Eq.refl =
      Eq.trans (cK-a {a = idx s} {idx s′} p (idx y))
        (Eq.trans (Eq.cong₂ _+_ (δᶠ-idx s y) (δᶠ-idx s′ y)) (Eq.sym (kOp-i s s′ y)))

    at-s′ : ∀ v → v ≡ s′ → s ≢ s′ →
            coefℤ (TL.K-gen (idx s) (idx s′) p) (idx v) (idx y) ≡ kOp s s′ v y
    at-s′ v Eq.refl ne =
      Eq.trans (cK-b {a = idx s} {idx s′} p (idx y))
        (Eq.trans (Eq.cong₂ (λ u w → u + - w) (δᶠ-idx s y) (δᶠ-idx s′ y))
          (Eq.trans (Eq.cong (δb s y +_) (Eq.sym (-1*x (δb s′ y))))
            (Eq.sym (kOp-j s s′ y ne))))

    go : Dec (idx x ≡ idx s) → Dec (idx x ≡ idx s′) →
         coefℤ (TL.K-gen (idx s) (idx s′) p) (idx x) (idx y) ≡ kOp s s′ x y
    go (yes e) _ = at-s x (idx-inj {x} {s} e)
    go (no ne) (yes e) = at-s′ x (idx-inj {x} {s′} e) (λ e′ → ne (Eq.trans e (Eq.sym (Eq.cong idx e′))))
    go (no ne) (no ne′) =
      Eq.trans (cK-≢ {a = idx s} {idx s′} p ne ne′ (idx y))
        (Eq.trans (Eq.cong (γ *_) (δᶠ-idx x y))
          (Eq.sym (kOp-other s s′ x y
            (eqB-false x s (λ e → ne (Eq.cong idx e))) (eqB-false x s′ (λ e → ne′ (Eq.cong idx e))))))

  ----------------------------------------------------------------------
  -- The reversed spelling: (−1)_[s] K_[s′,s] (−1)_[s′] is K on (s , s′)

  -- The sign −1 at a basis vector.
  neg : Bits n → Bits n → 𝔽
  neg s x = if eqB x s then -1# else 1#

  phs² : ∀ s x → phs s x * phs s x ≡ neg s x
  phs² s x with eqB x s
  ... | true  = Eq.refl
  ... | false = Eq.refl

  -- A diagonal on the left scales the rows, on the right the columns.
  diag-left : ∀ (f : Bits n → 𝔽) (M : Op n) → (diag f ⊙ M) ≐ (λ x y → f x * M x y)
  diag-left f M x y =
    Eq.trans (Σ-cong (λ z → *-assoc (f x) (δb x z) (M z y)))
      (Eq.trans (Σ-scaleˡ (f x) (λ z → δb x z * M z y)) (Eq.cong (f x *_) (Σ-δˡ x (λ z → M z y))))

  diag-right : ∀ (M : Op n) (g : Bits n → 𝔽) → (M ⊙ diag g) ≐ (λ x y → M x y * g y)
  diag-right M g x y =
    Eq.trans (Σ-cong (λ z → Eq.trans (Eq.sym (*-assoc (M x z) (g z) (δb z y)))
                                   (Eq.cong (_* δb z y) (*-comm (M x z) (g z)))))
      (Eq.trans (Σ-δʳ y (λ z → g z * M x z)) (*-comm (g y) (M x y)))

  -- The rows of the conjugate, pointwise.
  rev-K : ∀ s s′ → s ≢ s′ →
          (λ x y → neg s x * (kOp s′ s x y * neg s′ y)) ≐ kOp s s′
  rev-K s s′ ne x y = bool-cases (eqB x s) row-s (λ xs → bool-cases (eqB x s′) (row-s′ xs) (row-other xs))
    where
    s′≢s : s′ ≢ s
    s′≢s e = ne (Eq.sym e)

    -- δ at y, in the three positions.
    δ-at : ∀ y → y ≡ s → δb s y ≡ 1# × δb s′ y ≡ 0# × neg s′ y ≡ 1#
    δ-at y ys = Eq.trans (δ-eq s y) (if-true 1# 0# (eqB-complete y s ys)) ,
                Eq.trans (δ-eq s′ y) (if-false 1# 0# (eqB-false y s′ (λ e → ne (Eq.trans (Eq.sym ys) e)))) ,
                if-false -1# 1# (eqB-false y s′ (λ e → ne (Eq.trans (Eq.sym ys) e)))

    δ-at′ : ∀ y → y ≡ s′ → δb s y ≡ 0# × δb s′ y ≡ 1# × neg s′ y ≡ -1#
    δ-at′ y ys′ = Eq.trans (δ-eq s y) (if-false 1# 0# (eqB-false y s (λ e → ne (Eq.trans (Eq.sym e) ys′)))) ,
                  Eq.trans (δ-eq s′ y) (if-true 1# 0# (eqB-complete y s′ ys′)) ,
                  if-true -1# 1# (eqB-complete y s′ ys′)

    δ-off : ∀ y → eqB y s ≡ false → eqB y s′ ≡ false → δb s y ≡ 0# × δb s′ y ≡ 0# × neg s′ y ≡ 1#
    δ-off y ys ys′ = Eq.trans (δ-eq s y) (if-false 1# 0# ys) ,
                     Eq.trans (δ-eq s′ y) (if-false 1# 0# ys′) ,
                     if-false -1# 1# ys′

    -- The row of s.
    row-s : eqB x s ≡ true → neg s x * (kOp s′ s x y * neg s′ y) ≡ kOp s s′ x y
    row-s xs = Eq.subst (λ x → neg s x * (kOp s′ s x y * neg s′ y) ≡ kOp s s′ x y) (Eq.sym (eqB-sound x s xs))
      (Eq.trans (Eq.cong₂ _*_ (if-true -1# 1# (eqB-refl s)) (Eq.cong (_* neg s′ y) (kOp-j s′ s y s′≢s)))
        (Eq.trans goal (Eq.sym (kOp-i s s′ y))))
      where
      goal : -1# * ((δb s′ y + -1# * δb s y) * neg s′ y) ≡ δb s y + δb s′ y
      goal = bool-cases (eqB y s)
        (λ ys → let (a , b , c) = δ-at y (eqB-sound y s ys) in
                by3 {λ A B C → -1# * ((B + -1# * A) * C) ≡ A + B} a b c Eq.refl)
        (λ ys → bool-cases (eqB y s′)
          (λ ys′ → let (a , b , c) = δ-at′ y (eqB-sound y s′ ys′) in
                   by3 {λ A B C → -1# * ((B + -1# * A) * C) ≡ A + B} a b c Eq.refl)
          (λ ys′ → let (a , b , c) = δ-off y ys ys′ in
                   by3 {λ A B C → -1# * ((B + -1# * A) * C) ≡ A + B} a b c Eq.refl))

    -- The row of s′.
    row-s′ : eqB x s ≡ false → eqB x s′ ≡ true → neg s x * (kOp s′ s x y * neg s′ y) ≡ kOp s s′ x y
    row-s′ xs xs′ = Eq.subst (λ x → neg s x * (kOp s′ s x y * neg s′ y) ≡ kOp s s′ x y) (Eq.sym (eqB-sound x s′ xs′))
      (Eq.trans (Eq.cong₂ _*_ (if-false -1# 1# (eqB-false s′ s s′≢s)) (Eq.cong (_* neg s′ y) (kOp-i s′ s y)))
        (Eq.trans goal (Eq.sym (kOp-j s s′ y ne))))
      where
      goal : 1# * ((δb s′ y + δb s y) * neg s′ y) ≡ δb s y + -1# * δb s′ y
      goal = bool-cases (eqB y s)
        (λ ys → let (a , b , c) = δ-at y (eqB-sound y s ys) in
                by3 {λ A B C → 1# * ((B + A) * C) ≡ A + -1# * B} a b c Eq.refl)
        (λ ys → bool-cases (eqB y s′)
          (λ ys′ → let (a , b , c) = δ-at′ y (eqB-sound y s′ ys′) in
                   by3 {λ A B C → 1# * ((B + A) * C) ≡ A + -1# * B} a b c Eq.refl)
          (λ ys′ → let (a , b , c) = δ-off y ys ys′ in
                   by3 {λ A B C → 1# * ((B + A) * C) ≡ A + -1# * B} a b c Eq.refl))

    -- The other rows.
    row-other : eqB x s ≡ false → eqB x s′ ≡ false → neg s x * (kOp s′ s x y * neg s′ y) ≡ kOp s s′ x y
    row-other xs xs′ =
      Eq.trans (Eq.cong₂ _*_ (if-false -1# 1# xs) (Eq.cong (_* neg s′ y) (kOp-other s′ s x y xs′ xs)))
        (Eq.trans goal (Eq.sym (kOp-other s s′ x y xs xs′)))
      where
      goal : 1# * ((γ * δb x y) * neg s′ y) ≡ γ * δb x y
      goal = bool-cases (eqB y s′)
        (λ ys′ → Eq.trans (Eq.cong (λ d → 1# * ((γ * d) * neg s′ y))
                            (Eq.trans (δ-eq x y) (if-false 1# 0# (Eq.trans (Eq.cong (λ v → eqB v x) (eqB-sound y s′ ys′)) (Eq.trans (eqB-sym s′ x) xs′)))))
                   (Eq.trans (Eq.cong (λ c → 1# * ((γ * 0#) * c)) (if-true -1# 1# ys′))
                     (Eq.sym (Eq.cong (γ *_) (Eq.trans (δ-eq x y) (if-false 1# 0# (Eq.trans (Eq.cong (λ v → eqB v x) (eqB-sound y s′ ys′)) (Eq.trans (eqB-sym s′ x) xs′))))))))
        (λ ys′ → Eq.trans (Eq.cong (λ c → 1# * ((γ * δb x y) * c)) (if-false -1# 1# ys′))
                   (Eq.trans (*-identityˡ _) (*-identityʳ _)))

  ----------------------------------------------------------------------
  -- The letter Kp, in either order

  -- Its scaled operator: scale 1, and K on (s , s′).
  Kp-M : ∀ (s s′ : Bits n) → s ≢ s′ → proj₂ ⟦ Kp (idx s) (idx s′) ⟧Y ≐ kOp s s′
  Kp-M s s′ ne = go (FinP.<-cmp (idx s) (idx s′))
    where
    go : Tri (idx s <ᶠ idx s′) (idx s ≡ idx s′) (idx s′ <ᶠ idx s) →
         proj₂ ⟦ Kp (idx s) (idx s′) ⟧Y ≐ kOp s s′
    go (tri< p _ _) =
      Eq.subst (λ w → proj₂ ⟦ w ⟧Y ≐ kOp s s′) (Eq.sym (Kp-< (idx s) (idx s′) p)) (K-M s s′ p)
    go (tri≈ _ e _) = ⊥-elim (ne (idx-inj e))
    go (tri> _ _ q) =
      Eq.subst (λ w → proj₂ ⟦ w ⟧Y ≐ kOp s s′) (Eq.sym (Kp-> (idx s) (idx s′) q))
        (≐-trans (⊙-cong (i-M s) (⊙-cong (i-M s) (⊙-cong (K-M s′ s q) (⊙-cong (i-M s′) (i-M s′)))))
        (≐-trans (⊙-cong (≐-refl (diag (phs s))) (⊙-cong (≐-refl (diag (phs s))) (⊙-cong (≐-refl (kOp s′ s))
                   (≐-trans (diag-⊙ (phs s′) (phs s′)) (diag-cong (phs² s′))))))
        (≐-trans (≐-sym (⊙-assoc (diag (phs s)) (diag (phs s)) (kOp s′ s ⊙ diag (neg s′))))
        (≐-trans (⊙-cong (≐-trans (diag-⊙ (phs s) (phs s)) (diag-cong (phs² s))) (diag-right (kOp s′ s) (neg s′)))
        (≐-trans (diag-left (neg s) (λ x y → kOp s′ s x y * neg s′ y))
                 (rev-K s s′ ne))))))

  Kp-ℓ : ∀ (s s′ : Bits n) → s ≢ s′ → proj₁ ⟦ Kp (idx s) (idx s′) ⟧Y ≡ 1
  Kp-ℓ s s′ ne = go (FinP.<-cmp (idx s) (idx s′))
    where
    go : Tri (idx s <ᶠ idx s′) (idx s ≡ idx s′) (idx s′ <ᶠ idx s) → proj₁ ⟦ Kp (idx s) (idx s′) ⟧Y ≡ 1
    go (tri< p _ _) = Eq.cong (λ w → proj₁ ⟦ w ⟧Y) (Kp-< (idx s) (idx s′) p)
    go (tri≈ _ e _) = ⊥-elim (ne (idx-inj e))
    go (tri> _ _ q) = Eq.cong (λ w → proj₁ ⟦ w ⟧Y) (Kp-> (idx s) (idx s′) q)

------------------------------------------------------------------------
-- The invariant

-- On the covered vectors, γ^f times K on wire p; on the others,
-- γ^(f + 1) times the identity.
part : ℕ → (Bits n → Bool) → ℕ → Op n
part p cov f x y = if cov x then (γ ^ f) * kWire p x y else (γ ^ suc f) * δb x y

private
  part-cong : ∀ p {cov cov′} f → (∀ x → cov x ≡ cov′ x) → part p cov f ≐ part p cov′ f
  part-cong p f e x y =
    Eq.cong (λ b → if b then (γ ^ f) * kWire p x y else (γ ^ suc f) * δb x y) (e x)

  part-true : ∀ p cov f x y → cov x ≡ true → part p cov f x y ≡ (γ ^ f) * kWire p x y
  part-true p cov f x y e = if-true ((γ ^ f) * kWire p x y) ((γ ^ suc f) * δb x y) e

  part-false : ∀ p cov f x y → cov x ≡ false → part p cov f x y ≡ (γ ^ suc f) * δb x y
  part-false p cov f x y e = if-false ((γ ^ f) * kWire p x y) ((γ ^ suc f) * δb x y) e

------------------------------------------------------------------------
-- One letter, on a pair of vectors differing at wire p

private
  -- i has bit p clear and j has it set, the other bits agreeing.
  module Pair (p : ℕ) (q : p < n) (i j : Bits n)
              (rem : removeℕ p i ≡ removeℕ p j)
              (li : lookupℕ p i ≡ false) (lj : lookupℕ p j ≡ true) where

    private
      p≤ : p ≤ ₃₊ m
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

      -- K on wire p, on the pair.
      kWire-i : ∀ y → kWire p i y ≡ δb i y + δb j y
      kWire-i y = bool-cases (eqB (removeℕ p i) (removeℕ p y)) on off
        where
        off : eqB (removeℕ p i) (removeℕ p y) ≡ false → kWire p i y ≡ δb i y + δb j y
        off e = let (di , dj) = δ-off y e in
          Eq.trans (if-false (kval (lookupℕ p i) (lookupℕ p y)) 0# e)
            (Eq.sym (Eq.trans (Eq.cong₂ _+_ di dj) (+-identityˡ 0#)))
        on : eqB (removeℕ p i) (removeℕ p y) ≡ true → kWire p i y ≡ δb i y + δb j y
        on e with in-pair y e
        ... | inj₁ yi = let (di , dj) = δ-at y yi in
          Eq.trans (if-true (kval (lookupℕ p i) (lookupℕ p y)) 0# e)
            (Eq.trans (Eq.cong₂ kval li (Eq.trans (Eq.cong (lookupℕ p) yi) li))
              (Eq.sym (Eq.trans (Eq.cong₂ _+_ di dj) (+-identityʳ 1#))))
        ... | inj₂ yj = let (di , dj) = δ-at′ y yj in
          Eq.trans (if-true (kval (lookupℕ p i) (lookupℕ p y)) 0# e)
            (Eq.trans (Eq.cong₂ kval li (Eq.trans (Eq.cong (lookupℕ p) yj) lj))
              (Eq.sym (Eq.trans (Eq.cong₂ _+_ di dj) (+-identityˡ 1#))))

      kWire-j : ∀ y → kWire p j y ≡ δb i y + -1# * δb j y
      kWire-j y = bool-cases (eqB (removeℕ p i) (removeℕ p y)) on off
        where
        rem-j : eqB (removeℕ p j) (removeℕ p y) ≡ eqB (removeℕ p i) (removeℕ p y)
        rem-j = Eq.cong (λ v → eqB v (removeℕ p y)) (Eq.sym rem)
        off : eqB (removeℕ p i) (removeℕ p y) ≡ false → kWire p j y ≡ δb i y + -1# * δb j y
        off e = let (di , dj) = δ-off y e in
          Eq.trans (if-false (kval (lookupℕ p j) (lookupℕ p y)) 0# (Eq.trans rem-j e))
            (Eq.sym (Eq.trans (Eq.cong₂ (λ u v → u + -1# * v) di dj)
                      (Eq.trans (Eq.cong (0# +_) (*-zeroʳ -1#)) (+-identityˡ 0#))))
        on : eqB (removeℕ p i) (removeℕ p y) ≡ true → kWire p j y ≡ δb i y + -1# * δb j y
        on e with in-pair y e
        ... | inj₁ yi = let (di , dj) = δ-at y yi in
          Eq.trans (if-true (kval (lookupℕ p j) (lookupℕ p y)) 0# (Eq.trans rem-j e))
            (Eq.trans (Eq.cong₂ kval lj (Eq.trans (Eq.cong (lookupℕ p) yi) li))
              (Eq.sym (Eq.trans (Eq.cong₂ (λ u v → u + -1# * v) di dj)
                        (Eq.trans (Eq.cong (1# +_) (*-zeroʳ -1#)) (+-identityʳ 1#)))))
        ... | inj₂ yj = let (di , dj) = δ-at′ y yj in
          Eq.trans (if-true (kval (lookupℕ p j) (lookupℕ p y)) 0# (Eq.trans rem-j e))
            (Eq.trans (Eq.cong₂ kval lj (Eq.trans (Eq.cong (lookupℕ p) yj) lj))
              (Eq.sym (Eq.trans (Eq.cong₂ (λ u v → u + -1# * v) di dj)
                        (Eq.trans (Eq.cong (0# +_) (*-identityʳ -1#)) (+-identityˡ -1#)))))

    -- The letter alone: the first step, from the identity.
    first : ∀ (cov : Bits n → Bool) → (∀ x → cov x ≡ false) →
            kOp i j ≐ part p (λ x → cov x ∨ eqB x i ∨ eqB x j) 0
    first cov c₀ x y = bool-cases (eqB x i)
      (λ xi → Eq.subst (λ v → kOp i j v y ≡ part p cov′ 0 v y) (Eq.sym (eqB-sound x i xi)) row-i)
      (λ xi → bool-cases (eqB x j)
        (λ xj → Eq.subst (λ v → kOp i j v y ≡ part p cov′ 0 v y) (Eq.sym (eqB-sound x j xj)) row-j)
        (λ xj → row-other xi xj))
      where
      cov′ : Bits n → Bool
      cov′ x = cov x ∨ eqB x i ∨ eqB x j
      row-i : kOp i j i y ≡ part p cov′ 0 i y
      row-i = Eq.trans (kOp-i i j y)
        (Eq.trans (Eq.sym (kWire-i y))
          (Eq.trans (Eq.sym (*-identityˡ (kWire p i y)))
            (Eq.sym (part-true p cov′ 0 i y (Eq.cong₂ _∨_ (c₀ i) (Eq.cong (_∨ eqB i j) (eqB-refl i)))))))
      row-j : kOp i j j y ≡ part p cov′ 0 j y
      row-j = Eq.trans (kOp-j i j y i≢j)
        (Eq.trans (Eq.sym (kWire-j y))
          (Eq.trans (Eq.sym (*-identityˡ (kWire p j y)))
            (Eq.sym (part-true p cov′ 0 j y (Eq.cong₂ _∨_ (c₀ j) (Eq.cong₂ _∨_ (eqB-false j i j≢i) (eqB-refl j)))))))
      row-other : eqB x i ≡ false → eqB x j ≡ false → kOp i j x y ≡ part p cov′ 0 x y
      row-other xi xj = Eq.trans (kOp-other i j x y xi xj)
        (Eq.trans (Eq.cong (_* δb x y) (Eq.sym (*-identityʳ γ)))
          (Eq.sym (part-false p cov′ 0 x y
            (Eq.trans (Eq.cong (cov x ∨_) (Eq.cong₂ _∨_ xi xj)) (Eq.trans (∨-identityʳ (cov x)) (c₀ x))))))

    -- The letter on the invariant: one step.
    step : ∀ (cov : Bits n → Bool) f → cov i ≡ false → cov j ≡ false →
           (kOp i j ⊙ part p cov f) ≐ part p (λ x → cov x ∨ eqB x i ∨ eqB x j) (suc f)
    step cov f ci cj x y = bool-cases (eqB x i)
      (λ xi → Eq.subst (λ v → Σb (λ z → kOp i j v z * M z y) ≡ part p cov′ (suc f) v y)
                (Eq.sym (eqB-sound x i xi)) row-i)
      (λ xi → bool-cases (eqB x j)
        (λ xj → Eq.subst (λ v → Σb (λ z → kOp i j v z * M z y) ≡ part p cov′ (suc f) v y)
                  (Eq.sym (eqB-sound x j xj)) row-j)
        (λ xj → row-other xi xj))
      where
      open Eq.≡-Reasoning
      M : Op n
      M = part p cov f
      cov′ : Bits n → Bool
      cov′ x = cov x ∨ eqB x i ∨ eqB x j
      row-i : Σb (λ z → kOp i j i z * M z y) ≡ part p cov′ (suc f) i y
      row-i = begin
        Σb (λ z → kOp i j i z * M z y)
          ≡⟨ Σ-cong (λ z → Eq.cong (_* M z y) (kOp-i i j z)) ⟩
        Σb (λ z → (δb i z + δb j z) * M z y)
          ≡⟨ Σ-cong (λ z → *-distribʳ-+ (M z y) (δb i z) (δb j z)) ⟩
        Σb (λ z → δb i z * M z y + δb j z * M z y)
          ≡⟨ Σ-add (λ z → δb i z * M z y) (λ z → δb j z * M z y) ⟩
        Σb (λ z → δb i z * M z y) + Σb (λ z → δb j z * M z y)
          ≡⟨ Eq.cong₂ _+_ (Σ-δˡ i (λ z → M z y)) (Σ-δˡ j (λ z → M z y)) ⟩
        M i y + M j y
          ≡⟨ Eq.cong₂ _+_ (part-false p cov f i y ci) (part-false p cov f j y cj) ⟩
        (γ ^ suc f) * δb i y + (γ ^ suc f) * δb j y
          ≡⟨ fac+ (γ ^ suc f) (δb i y) (δb j y) ⟩
        (γ ^ suc f) * (δb i y + δb j y)
          ≡⟨ Eq.cong ((γ ^ suc f) *_) (Eq.sym (kWire-i y)) ⟩
        (γ ^ suc f) * kWire p i y
          ≡⟨ Eq.sym (part-true p cov′ (suc f) i y (Eq.cong₂ _∨_ ci (Eq.cong (_∨ eqB i j) (eqB-refl i)))) ⟩
        part p cov′ (suc f) i y ∎
      row-j : Σb (λ z → kOp i j j z * M z y) ≡ part p cov′ (suc f) j y
      row-j = begin
        Σb (λ z → kOp i j j z * M z y)
          ≡⟨ Σ-cong (λ z → Eq.cong (_* M z y) (kOp-j i j z i≢j)) ⟩
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
        (γ ^ suc f) * δb i y + -1# * ((γ ^ suc f) * δb j y)
          ≡⟨ fac− (γ ^ suc f) (δb i y) (δb j y) ⟩
        (γ ^ suc f) * (δb i y + -1# * δb j y)
          ≡⟨ Eq.cong ((γ ^ suc f) *_) (Eq.sym (kWire-j y)) ⟩
        (γ ^ suc f) * kWire p j y
          ≡⟨ Eq.sym (part-true p cov′ (suc f) j y (Eq.cong₂ _∨_ cj (Eq.cong₂ _∨_ (eqB-false j i j≢i) (eqB-refl j)))) ⟩
        part p cov′ (suc f) j y ∎
      row-other : eqB x i ≡ false → eqB x j ≡ false →
                  Σb (λ z → kOp i j x z * M z y) ≡ part p cov′ (suc f) x y
      row-other xi xj = begin
        Σb (λ z → kOp i j x z * M z y)
          ≡⟨ Σ-cong (λ z → Eq.cong (_* M z y) (kOp-other i j x z xi xj)) ⟩
        Σb (λ z → (γ * δb x z) * M z y)
          ≡⟨ Σ-cong (λ z → *-assoc γ (δb x z) (M z y)) ⟩
        Σb (λ z → γ * (δb x z * M z y))
          ≡⟨ Σ-scaleˡ γ (λ z → δb x z * M z y) ⟩
        γ * Σb (λ z → δb x z * M z y)
          ≡⟨ Eq.cong (γ *_) (Σ-δˡ x (λ z → M z y)) ⟩
        γ * M x y
          ≡⟨ lift ⟩
        part p cov′ (suc f) x y ∎
        where
        c′x : cov′ x ≡ cov x
        c′x = Eq.trans (Eq.cong (cov x ∨_) (Eq.cong₂ _∨_ xi xj)) (∨-identityʳ (cov x))
        lift : γ * M x y ≡ part p cov′ (suc f) x y
        lift = bool-cases (cov x)
          (λ cx → begin
             γ * M x y
               ≡⟨ Eq.cong (γ *_) (part-true p cov f x y cx) ⟩
             γ * ((γ ^ f) * kWire p x y)
               ≡⟨ Eq.sym (*-assoc γ (γ ^ f) (kWire p x y)) ⟩
             (γ ^ suc f) * kWire p x y
               ≡⟨ Eq.sym (part-true p cov′ (suc f) x y (Eq.trans c′x cx)) ⟩
             part p cov′ (suc f) x y ∎)
          (λ cx → begin
             γ * M x y
               ≡⟨ Eq.cong (γ *_) (part-false p cov f x y cx) ⟩
             γ * ((γ ^ suc f) * δb x y)
               ≡⟨ Eq.sym (*-assoc γ (γ ^ suc f) (δb x y)) ⟩
             (γ ^ suc (suc f)) * δb x y
               ≡⟨ Eq.sym (part-false p cov′ (suc f) x y (Eq.trans c′x cx)) ⟩
             part p cov′ (suc f) x y ∎)

------------------------------------------------------------------------
-- The product over all contexts

private
  module Encode (p : ℕ) (q : p < n) where

    private
      p≤ : p ≤ ₃₊ m
      p≤ = ≤-pred q

      -- The vectors of a context: bit b at wire p.
      v : Bits (₃₊ m) → Bool → Bits n
      v c b = str₁ p c b

      ctx : Bits n → Bits (₃₊ m)
      ctx x = removeℕ p x

      rem-v : ∀ c → removeℕ p (v c false) ≡ removeℕ p (v c true)
      rem-v c = Eq.trans (remove-insert p false c p≤) (Eq.sym (remove-insert p true c p≤))

      bit-v : ∀ c b → lookupℕ p (v c b) ≡ b
      bit-v c b = lookup-insert p b c p≤

      ctx-v : ∀ c b → ctx (v c b) ≡ c
      ctx-v c b = remove-insert p b c p≤

      v-ctx : ∀ x → x ≡ v (ctx x) (lookupℕ p x)
      v-ctx x = Eq.sym (insert-lookup-remove p x p≤)

      v-bit : ∀ c → v c false ≢ v c true
      v-bit c e = true≢false
        (Eq.trans (Eq.sym (bit-v c true)) (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym e)) (bit-v c false)))

    -- The word, the letter of a context and the cover of a list of
    -- contexts.
    word : List (Bits (₃₊ m)) → Word (TL.Gen N)
    word cs = ∏ cs (λ c → Kp (idx (v c false)) (idx (v c true)))

    L : Bits (₃₊ m) → Op n
    L c = kOp (v c false) (v c true)

    cov : List (Bits (₃₊ m)) → Bits n → Bool
    cov cs x = ctx x ∈ᵇ cs

    partL : List (Bits (₃₊ m)) → Op n
    partL []       = Idₒ
    partL (c ∷ cs) = part p (cov (c ∷ cs)) (length cs)

    private
      module P (c : Bits (₃₊ m)) = Pair p q (v c false) (v c true) (rem-v c) (bit-v c false) (bit-v c true)

      -- The cover after a context, and its canonical form.
      cov₁ : List (Bits (₃₊ m)) → Bits (₃₊ m) → Bits n → Bool
      cov₁ cs c x = cov cs x ∨ eqB x (v c false) ∨ eqB x (v c true)

      cov-∷ : ∀ cs c x → cov₁ cs c x ≡ cov (c ∷ cs) x
      cov-∷ cs c x = bool-cases (eqB (ctx x) c) here there
        where
        -- The context of x is c: x is one of its two vectors.
        here : eqB (ctx x) c ≡ true → cov₁ cs c x ≡ cov (c ∷ cs) x
        here ec = Eq.trans lhs (Eq.sym (Eq.cong (_∨ (ctx x ∈ᵇ cs)) ec))
          where
          x≡ : x ≡ v c (lookupℕ p x)
          x≡ = Eq.trans (v-ctx x) (Eq.cong (λ c′ → v c′ (lookupℕ p x)) (eqB-sound (ctx x) c ec))
          lhs : cov₁ cs c x ≡ true
          lhs = bool-cases (lookupℕ p x)
            (λ lg → Eq.trans (Eq.cong (λ b → cov cs x ∨ eqB x (v c false) ∨ b)
                                (eqB-complete x _ (Eq.trans x≡ (Eq.cong (v c) lg))))
                             (Eq.trans (Eq.cong (cov cs x ∨_) (∨-true (eqB x (v c false)))) (∨-true (cov cs x))))
            (λ lg → Eq.trans (Eq.cong (λ b → cov cs x ∨ b ∨ eqB x (v c true))
                                (eqB-complete x _ (Eq.trans x≡ (Eq.cong (v c) lg))))
                             (∨-true (cov cs x)))
            where
            ∨-true : ∀ a → a ∨ true ≡ true
            ∨-true true  = Eq.refl
            ∨-true false = Eq.refl
        -- The context of x is not c: x is neither.
        there : eqB (ctx x) c ≡ false → cov₁ cs c x ≡ cov (c ∷ cs) x
        there ec = Eq.trans lhs (Eq.sym (Eq.cong (_∨ (ctx x ∈ᵇ cs)) ec))
          where
          no-v : ∀ b → eqB x (v c b) ≡ false
          no-v b = eqB-false x _ (λ e → true≢false
            (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ y → eqB (ctx y) c) e)
                                        (Eq.trans (Eq.cong (λ y → eqB y c) (ctx-v c b)) (eqB-refl c))))
                      ec))
          lhs : cov₁ cs c x ≡ cov cs x
          lhs = Eq.trans (Eq.cong (cov cs x ∨_) (Eq.cong₂ _∨_ (no-v false) (no-v true))) (∨-identityʳ (cov cs x))

      -- A context not yet processed: its vectors are uncovered.
      unc : ∀ cs c → c ∈ᵇ cs ≡ false → ∀ b → cov cs (v c b) ≡ false
      unc cs c nc b = Eq.trans (Eq.cong (_∈ᵇ cs) (ctx-v c b)) nc

      -- The first context, from the identity.
      ctx-first : ∀ c → (L c ⊙ Idₒ) ≐ part p (cov₁ [] c) 0
      ctx-first c = ≐-trans (⊙-identityʳ (L c)) (P.first c (cov []) (λ x → Eq.refl))

      -- The product of the letters over a list of distinct contexts.
      fold : ∀ cs → Nodup cs → foldr (λ c M → L c ⊙ M) Idₒ cs ≐ partL cs
      fold []            _         = ≐-refl Idₒ
      fold (c ∷ [])      _         = ≐-trans (ctx-first c) (part-cong p 0 (cov-∷ [] c))
      fold (c ∷ c′ ∷ cs) (nc , nd) =
        ≐-trans (⊙-cong (≐-refl (L c)) (fold (c′ ∷ cs) nd))
          (≐-trans (P.step c (cov (c′ ∷ cs)) (length cs) (unc (c′ ∷ cs) c nc false) (unc (c′ ∷ cs) c nc true))
                   (part-cong p (suc (length cs)) (cov-∷ (c′ ∷ cs) c)))

      -- With every context covered, the invariant is the gate.
      final : ∀ cs → (∀ x → ctx x ∈ᵇ cs ≡ true) → cs ≢ [] →
              (γ · partL cs) ≐ ((γ ^ length cs) · kWire p)
      final []       _   ne = ⊥-elim (ne Eq.refl)
      final (c ∷ cs) all _  x y =
        Eq.trans (Eq.cong (γ *_) (part-true p (cov (c ∷ cs)) (length cs) x y (all x)))
                 (Eq.sym (*-assoc γ (γ ^ length cs) (kWire p x y)))

      -- The reading of the word.
      word-M : ∀ cs → Nodup cs → proj₂ ⟦ word cs ⟧Y ≐ partL cs
      word-M cs nd =
        ≐-trans (∏-M cs (λ c → Kp (idx (v c false)) (idx (v c true))))
          (≐-trans (fold-cong cs (λ c → Kp-M (v c false) (v c true) (v-bit c))) (fold cs nd))

      word-ℓ : ∀ cs → proj₁ ⟦ word cs ⟧Y ≡ length cs
      word-ℓ cs = Eq.trans (∏-ℓ cs (λ c → Kp (idx (v c false)) (idx (v c true)))) (sum cs)
        where
        sum : ∀ cs → foldr (λ c f → proj₁ ⟦ Kp (idx (v c false)) (idx (v c true)) ⟧Y +ℕ f) 0 cs ≡ length cs
        sum []       = Eq.refl
        sum (c ∷ cs) = Eq.cong₂ _+ℕ_ (Kp-ℓ (v c false) (v c true) (v-bit c)) (sum cs)

      γ^1 : γ^ 1 ≡ γ
      γ^1 = Eq.trans (γ^-def 1) (*-identityʳ γ)

    -- The word over every context is the gate.
    sem : ∀ cs → Nodup cs → (∀ x → ctx x ∈ᵇ cs ≡ true) → cs ≢ [] →
          ⟦ word cs ⟧Y ~ (1 , kWire p)
    sem cs nd all ne =
      ≐-trans (·-cong γ^1 (word-M cs nd))
        (≐-trans (final cs all ne)
                 (·-cong (Eq.trans (Eq.sym (γ^-def (length cs))) (Eq.cong γ^_ (Eq.sym (word-ℓ cs)))) (≐-refl (kWire p))))

------------------------------------------------------------------------
-- K on wire p

private
  nonempty : ∀ {k} (c : Bits k) → allBits k ≢ []
  nonempty {k} c e = true≢false (Eq.trans (Eq.sym (∈-allBits c)) (Eq.cong (c ∈ᵇ_) e))

E-K-sem : ∀ p → p < n → ⟦ E-K p ⟧Y ~ (1 , kWire p)
E-K-sem p q =
  Encode.sem p q (allBits (₃₊ m)) (allBits-nodup (₃₊ m)) (λ x → ∈-allBits (removeℕ p x))
    (nonempty (replicate (₃₊ m) false))
