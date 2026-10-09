------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators acting on a scaled column w / 2ᵏ, through its
-- numerator w ∈ ℤⁿ: (-1)_[a] and X_[a,b] keep the exponent, K_[a,b,c,d]
-- raises it by one (its scalar is 1/2), doubling the other entries.
-- This turns the column computations of the synthesis algorithm and of
-- the Main Lemma into arithmetic in ℤ.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.ColumnAction where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
open import Examples.Groups.CCX+HH-TwoLevel.Scale
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; scV-!)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The actions on numerators

Mᶻ : Fin n → Vec ℤ n → Vec ℤ n
Mᶻ a w = set₁ a (ℤ.- (w ! a)) w

Xᶻ : Fin n → Fin n → Vec ℤ n → Vec ℤ n
Xᶻ a b w = set₂ a b (w ! b) (w ! a) w

-- Signed sums of four integers.
linℤ : (s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ : ℤ) → ℤ
linℤ s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ = s₁ ℤ.* x₁ ℤ.+ s₂ ℤ.* x₂ ℤ.+ s₃ ℤ.* x₃ ℤ.+ s₄ ℤ.* x₄

p1ᶻ m1ᶻ : ℤ
p1ᶻ = + 1
m1ᶻ = -[1+ 0 ]

-- The rows of 2K.
rowAᶻ rowBᶻ rowCᶻ rowDᶻ : (x₁ x₂ x₃ x₄ : ℤ) → ℤ
rowAᶻ = linℤ p1ᶻ p1ᶻ p1ᶻ p1ᶻ
rowBᶻ = linℤ p1ᶻ m1ᶻ p1ᶻ m1ᶻ
rowCᶻ = linℤ p1ᶻ p1ᶻ m1ᶻ m1ᶻ
rowDᶻ = linℤ p1ᶻ m1ᶻ m1ᶻ p1ᶻ

-- K at scale k + 1: the other entries are doubled.
Kᶻ : (a b c d : Fin n) → Vec ℤ n → Vec ℤ n
Kᶻ a b c d w =
  set₄ a b c d (rowAᶻ (w ! a) (w ! b) (w ! c) (w ! d)) (rowBᶻ (w ! a) (w ! b) (w ! c) (w ! d))
               (rowCᶻ (w ! a) (w ! b) (w ! c) (w ! d)) (rowDᶻ (w ! a) (w ! b) (w ! c) (w ! d))
               (Vec.map (+ 2 ℤ.*_) w)

------------------------------------------------------------------------
-- The rows of K on scaled entries

lin-sc : ∀ k s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ →
         lin (ι s₁) (ι s₂) (ι s₃) (ι s₄) (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄)
         ≡ sc (suc k) (linℤ s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄)
lin-sc k s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ = begin
  ½ᴰ DR.* (ι s₁ DR.* sc k x₁ DR.+ ι s₂ DR.* sc k x₂ DR.+ ι s₃ DR.* sc k x₃ DR.+ ι s₄ DR.* sc k x₄)
    ≡⟨ cong (½ᴰ DR.*_) (cong₂ DR._+_ (cong₂ DR._+_ (cong₂ DR._+_ (t s₁ x₁) (t s₂ x₂)) (t s₃ x₃)) (t s₄ x₄)) ⟩
  ½ᴰ DR.* (sc k (s₁ ℤ.* x₁) DR.+ sc k (s₂ ℤ.* x₂) DR.+ sc k (s₃ ℤ.* x₃) DR.+ sc k (s₄ ℤ.* x₄))
    ≡⟨ cong (½ᴰ DR.*_) (sym (trans (sc-+ k _ _) (cong (DR._+ sc k (s₄ ℤ.* x₄))
                                (trans (sc-+ k _ _) (cong (DR._+ sc k (s₃ ℤ.* x₃)) (sc-+ k _ _)))))) ⟩
  ½ᴰ DR.* sc k (linℤ s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄)
    ≡⟨ ½-sc k _ ⟩
  sc (suc k) (linℤ s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄) ∎
  where
  open ≡-Reasoning
  t : ∀ s x → ι s DR.* sc k x ≡ sc k (s ℤ.* x)
  t s x = sym (sc-* k s x)

private
  m1≡ : m1 ≡ ι m1ᶻ
  m1≡ = sym (ι-neg (+ 1))

rowA-sc : ∀ k x₁ x₂ x₃ x₄ → rowA (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄) ≡ sc (suc k) (rowAᶻ x₁ x₂ x₃ x₄)
rowA-sc k = lin-sc k p1ᶻ p1ᶻ p1ᶻ p1ᶻ

rowB-sc : ∀ k x₁ x₂ x₃ x₄ → rowB (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄) ≡ sc (suc k) (rowBᶻ x₁ x₂ x₃ x₄)
rowB-sc k x₁ x₂ x₃ x₄ =
  trans (cong (λ m → lin DR.1# m DR.1# m (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄)) m1≡) (lin-sc k p1ᶻ m1ᶻ p1ᶻ m1ᶻ x₁ x₂ x₃ x₄)

rowC-sc : ∀ k x₁ x₂ x₃ x₄ → rowC (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄) ≡ sc (suc k) (rowCᶻ x₁ x₂ x₃ x₄)
rowC-sc k x₁ x₂ x₃ x₄ =
  trans (cong (λ m → lin DR.1# DR.1# m m (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄)) m1≡) (lin-sc k p1ᶻ p1ᶻ m1ᶻ m1ᶻ x₁ x₂ x₃ x₄)

rowD-sc : ∀ k x₁ x₂ x₃ x₄ → rowD (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄) ≡ sc (suc k) (rowDᶻ x₁ x₂ x₃ x₄)
rowD-sc k x₁ x₂ x₃ x₄ =
  trans (cong (λ m → lin DR.1# m m DR.1# (sc k x₁) (sc k x₂) (sc k x₃) (sc k x₄)) m1≡) (lin-sc k p1ᶻ m1ᶻ m1ᶻ p1ᶻ x₁ x₂ x₃ x₄)

------------------------------------------------------------------------
-- The generators on scaled vectors

-- (The case analyses are by dec-elim rather than with-abstraction,
-- which would normalise the goals.)

actV-M : (a : Fin n) (k : ℕ) (w : Vec ℤ n) → actV (M-gen a) (scV k w) ≡ scV k (Mᶻ a w)
actV-M a k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (M-gen x) (scV k w) ! x                   ≡⟨ actV-Ma x (scV k w) ⟩
    DR.- (scV k w ! x)                             ≡⟨ cong DR.-_ (scV-! k w x) ⟩
    DR.- sc k (w ! x)                              ≡⟨ sym (sc-neg k (w ! x)) ⟩
    sc k (ℤ.- (w ! x))                             ≡⟨ cong (sc k) (sym (set₁-a x (ℤ.- (w ! x)) w)) ⟩
    sc k (Mᶻ x w ! x)                              ≡⟨ sym (scV-! k (Mᶻ x w) x) ⟩
    scV k (Mᶻ x w) ! x                             ∎ })
  (λ x≢a → begin
    actV (M-gen a) (scV k w) ! x                   ≡⟨ actV-M≢ a (scV k w) x≢a ⟩
    scV k w ! x                                    ≡⟨ scV-! k w x ⟩
    sc k (w ! x)                                   ≡⟨ cong (sc k) (sym (set₁-≢ a (ℤ.- (w ! a)) w x≢a)) ⟩
    sc k (Mᶻ a w ! x)                              ≡⟨ sym (scV-! k (Mᶻ a w) x) ⟩
    scV k (Mᶻ a w) ! x                             ∎)
  where open ≡-Reasoning

actV-X : (a b : Fin n) .(p : a < b) (k : ℕ) (w : Vec ℤ n) → actV (X-gen a b p) (scV k w) ≡ scV k (Xᶻ a b w)
actV-X a b p k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (X-gen x b p) v ! x                ≡⟨ actV-Xa p v ⟩
    v ! b                                   ≡⟨ scV-! k w b ⟩
    sc k (w ! b)                            ≡⟨ cong (sc k) (sym (set₂-a x b (w ! b) (w ! x) w)) ⟩
    sc k (Xᶻ x b w ! x)                     ≡⟨ sym (scV-! k (Xᶻ x b w) x) ⟩
    scV k (Xᶻ x b w) ! x                    ∎ })
  (λ x≢a → dec-elim (x FinP.≟ b)
    (λ { refl → begin
      actV (X-gen a x p) v ! x              ≡⟨ actV-Xb p v ⟩
      v ! a                                 ≡⟨ scV-! k w a ⟩
      sc k (w ! a)                          ≡⟨ cong (sc k) (sym (set₂-b a x (w ! x) (w ! a) w a≢b)) ⟩
      sc k (Xᶻ a x w ! x)                   ≡⟨ sym (scV-! k (Xᶻ a x w) x) ⟩
      scV k (Xᶻ a x w) ! x                  ∎ })
    (λ x≢b → begin
      actV (X-gen a b p) v ! x              ≡⟨ actV-X≢ p v x≢a x≢b ⟩
      v ! x                                 ≡⟨ scV-! k w x ⟩
      sc k (w ! x)                          ≡⟨ cong (sc k) (sym (set₂-≢ a b (w ! b) (w ! a) w x≢a x≢b)) ⟩
      sc k (Xᶻ a b w ! x)                   ≡⟨ sym (scV-! k (Xᶻ a b w) x) ⟩
      scV k (Xᶻ a b w) ! x                  ∎))
  where
  open ≡-Reasoning
  a≢b = <⇒≢ p
  v = scV k w

actV-K : (a b c d : Fin n) .(p : a < b) .(q : b < c) .(r : c < d) (k : ℕ) (w : Vec ℤ n) →
         actV (K-gen a b c d p q r) (scV k w) ≡ scV (suc k) (Kᶻ a b c d w)
actV-K a b c d p q r k w = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)
  where
  open ≡-Reasoning
  open Distinct₄ (distinct₄ p q r)
  D₄ = distinct₄ p q r
  g = K-gen a b c d p q r
  v = scV k w
  W = Kᶻ a b c d w
  -- The entries a, b, c and d of v.
  ents : ∀ (f : D → D → D → D → D) → f (v ! a) (v ! b) (v ! c) (v ! d) ≡ f (sc k (w ! a)) (sc k (w ! b)) (sc k (w ! c)) (sc k (w ! d))
  ents f = trans (cong (λ z → f z (v ! b) (v ! c) (v ! d)) (scV-! k w a))
             (trans (cong (λ z → f (sc k (w ! a)) z (v ! c) (v ! d)) (scV-! k w b))
               (trans (cong (λ z → f (sc k (w ! a)) (sc k (w ! b)) z (v ! d)) (scV-! k w c))
                 (cong (λ z → f (sc k (w ! a)) (sc k (w ! b)) (sc k (w ! c)) z) (scV-! k w d))))
  W! : ∀ x → scV (suc k) W ! x ≡ sc (suc k) (W ! x)
  W! = scV-! (suc k) W
  dw = Vec.map (+ 2 ℤ.*_) w
  at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → actV g v ! x ≡ scV (suc k) W ! x
  at x (yes refl) _ _ _ = begin
    actV g v ! x                     ≡⟨ actV-Ka p q r v ⟩
    rowA (v ! a) (v ! b) (v ! c) (v ! d) ≡⟨ ents rowA ⟩
    rowA (sc k (w ! a)) (sc k (w ! b)) (sc k (w ! c)) (sc k (w ! d)) ≡⟨ rowA-sc k _ _ _ _ ⟩
    sc (suc k) (rowAᶻ (w ! a) (w ! b) (w ! c) (w ! d)) ≡⟨ cong (sc (suc k)) (sym (set₄-a D₄ _ _ _ _ dw)) ⟩
    sc (suc k) (W ! x)               ≡⟨ sym (W! x) ⟩
    scV (suc k) W ! x                ∎
  at x (no _) (yes refl) _ _ = begin
    actV g v ! x                     ≡⟨ actV-Kb p q r v ⟩
    rowB (v ! a) (v ! b) (v ! c) (v ! d) ≡⟨ ents rowB ⟩
    rowB (sc k (w ! a)) (sc k (w ! b)) (sc k (w ! c)) (sc k (w ! d)) ≡⟨ rowB-sc k _ _ _ _ ⟩
    sc (suc k) (rowBᶻ (w ! a) (w ! b) (w ! c) (w ! d)) ≡⟨ cong (sc (suc k)) (sym (set₄-b D₄ _ _ _ _ dw)) ⟩
    sc (suc k) (W ! x)               ≡⟨ sym (W! x) ⟩
    scV (suc k) W ! x                ∎
  at x (no _) (no _) (yes refl) _ = begin
    actV g v ! x                     ≡⟨ actV-Kc p q r v ⟩
    rowC (v ! a) (v ! b) (v ! c) (v ! d) ≡⟨ ents rowC ⟩
    rowC (sc k (w ! a)) (sc k (w ! b)) (sc k (w ! c)) (sc k (w ! d)) ≡⟨ rowC-sc k _ _ _ _ ⟩
    sc (suc k) (rowCᶻ (w ! a) (w ! b) (w ! c) (w ! d)) ≡⟨ cong (sc (suc k)) (sym (set₄-c D₄ _ _ _ _ dw)) ⟩
    sc (suc k) (W ! x)               ≡⟨ sym (W! x) ⟩
    scV (suc k) W ! x                ∎
  at x (no _) (no _) (no _) (yes refl) = begin
    actV g v ! x                     ≡⟨ actV-Kd p q r v ⟩
    rowD (v ! a) (v ! b) (v ! c) (v ! d) ≡⟨ ents rowD ⟩
    rowD (sc k (w ! a)) (sc k (w ! b)) (sc k (w ! c)) (sc k (w ! d)) ≡⟨ rowD-sc k _ _ _ _ ⟩
    sc (suc k) (rowDᶻ (w ! a) (w ! b) (w ! c) (w ! d)) ≡⟨ cong (sc (suc k)) (sym (set₄-d D₄ _ _ _ _ dw)) ⟩
    sc (suc k) (W ! x)               ≡⟨ sym (W! x) ⟩
    scV (suc k) W ! x                ∎
  at x (no xa) (no xb) (no xc) (no xd) = begin
    actV g v ! x                     ≡⟨ actV-K≢ p q r v xa xb xc xd ⟩
    v ! x                            ≡⟨ scV-! k w x ⟩
    sc k (w ! x)                     ≡⟨ sym (sc-2 k (w ! x)) ⟩
    sc (suc k) (+ 2 ℤ.* (w ! x))     ≡⟨ cong (sc (suc k)) (sym (VecP.lookup-map x (+ 2 ℤ.*_) w)) ⟩
    sc (suc k) (dw ! x)              ≡⟨ cong (sc (suc k)) (sym (set₄-≢ D₄ _ _ _ _ dw xa xb xc xd)) ⟩
    sc (suc k) (W ! x)               ≡⟨ sym (W! x) ⟩
    scV (suc k) W ! x                ∎
