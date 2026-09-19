------------------------------------------------------------------------
-- Presentations of groups
--
-- The operator calculus behind the semantics of the multi-controlled
-- box: diagonal, permutation and controlled operators
--
-- Three shapes of operator on Bits n → Bits n → 𝔽 and the laws that
-- relate them, all pointwise:
--
--   * diagonal operators diag f, with f a function of the basis; they
--     compose by multiplying their entries and therefore commute
--     (diag-⊙, diag-comm).  Z on the bottom wire is one (Z-diag), and
--     so is the phase of the box, `phase k` — the sign −1 exactly when
--     wires 1 … k are all set — once the box is known to be diagonal;
--   * permutation operators, here the one transposition the box
--     needs, of wires 0 and 2 (sw, permOp); conjugating a diagonal
--     operator by it permutes its entries (perm-conj);
--   * controlled operators ctrl M N c: M on the bottom three wires
--     when the predicate c holds of the top ones, N otherwise.  They
--     compose componentwise (ctrl-⊙), which is the mixed product law
--     that makes the box's recursive step a computation on 8 × 8
--     matrices; a three-wire gate padded with idle wires is one
--     (emb-ctrl), and a controlled diagonal is diagonal (ctrl-diag).
--
-- Shifting an operator up a wire preserves scalars and diagonals
-- (up-·, up-diag).  Everything here is about operators, never about
-- circuits; Box applies it to the words of Definition 2.4.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Soundness.Operators where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Bool.Properties using (∧-identityʳ ; ∧-zeroʳ)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

import Data.Nat.Properties as NP

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation

private
  variable
    j k m n : ℕ

------------------------------------------------------------------------
-- Diagonal operators

-- The sign of a boolean: −1 when set.
sgn : Bool → 𝔽
sgn true  = -1#
sgn false = 1#

-- All wires set.
allT : Bits m → Bool
allT []       = true
allT (b ∷ bs) = b ∧ allT bs

-- The phase of the k-controlled box: −1 exactly when wires 1 … k are
-- all set; wire 0 does not count.
phase : (k : ℕ) → Bits (₁₊ k) → 𝔽
phase k (_ ∷ xs) = sgn (allT xs)

diag : (Bits n → 𝔽) → Op n
diag f x y = f x * δb x y

diag-cong : {f g : Bits n → 𝔽} → (∀ x → f x ≡ g x) → diag f ≐ diag g
diag-cong e x y = Eq.cong (_* δb x y) (e x)

private
  swapˡ : ∀ (a b c : 𝔽) → (a * b) * c ≡ b * (a * c)
  swapˡ a b c = Eq.trans (Eq.cong (_* c) (*-comm a b)) (*-assoc b a c)

  swapᵐ : ∀ (a b c : 𝔽) → a * (b * c) ≡ b * (a * c)
  swapᵐ a b c = Eq.trans (Eq.sym (*-assoc a b c)) (swapˡ a b c)

δb-∷ : ∀ (a b : Bool) (x y : Bits n) → δb (a ∷ x) (b ∷ y) ≡ δ₁ a b * δb x y
δb-∷ true  true  x y = Eq.sym (*-identityˡ (δb x y))
δb-∷ false false x y = Eq.sym (*-identityˡ (δb x y))
δb-∷ true  false x y = Eq.sym (*-zeroˡ (δb x y))
δb-∷ false true  x y = Eq.sym (*-zeroˡ (δb x y))

-- The delta splits over a three-bit prefix.
δb-₃ : ∀ (a b c a' b' c' : Bool) (x y : Bits n) →
       δb (a ∷ b ∷ c ∷ x) (a' ∷ b' ∷ c' ∷ y) ≡
       δb (a ∷ b ∷ c ∷ []) (a' ∷ b' ∷ c' ∷ []) * δb x y
δb-₃ a b c a' b' c' x y = begin
  δb (a ∷ b ∷ c ∷ x) (a' ∷ b' ∷ c' ∷ y)
    ≡⟨ δb-∷ a a' _ _ ⟩
  δ₁ a a' * δb (b ∷ c ∷ x) (b' ∷ c' ∷ y)
    ≡⟨ Eq.cong (δ₁ a a' *_) (δb-∷ b b' _ _) ⟩
  δ₁ a a' * (δ₁ b b' * δb (c ∷ x) (c' ∷ y))
    ≡⟨ Eq.cong (λ □ → δ₁ a a' * (δ₁ b b' * □)) (δb-∷ c c' x y) ⟩
  δ₁ a a' * (δ₁ b b' * (δ₁ c c' * δb x y))
    ≡⟨ Eq.sym (Eq.trans (Eq.cong (_* δb x y) (δb-₃-[] a b c a' b' c'))
                (Eq.trans (*-assoc _ _ _)
                  (Eq.cong (δ₁ a a' *_) (Eq.trans (*-assoc _ _ _)
                    (Eq.cong (δ₁ b b' *_) (Eq.cong (_* δb x y) (*-identityʳ (δ₁ c c')))))))) ⟩
  δb (a ∷ b ∷ c ∷ []) (a' ∷ b' ∷ c' ∷ []) * δb x y ∎
  where
  open Eq.≡-Reasoning
  δb-₃-[] : ∀ a b c a' b' c' →
            δb (a ∷ b ∷ c ∷ []) (a' ∷ b' ∷ c' ∷ []) ≡ δ₁ a a' * (δ₁ b b' * (δ₁ c c' * 1#))
  δb-₃-[] a b c a' b' c' =
    Eq.trans (δb-∷ a a' _ _)
      (Eq.cong (δ₁ a a' *_) (Eq.trans (δb-∷ b b' _ _)
        (Eq.cong (δ₁ b b' *_) (δb-∷ c c' [] []))))

-- Products of diagonal operators multiply the phases, so they commute.
diag-⊙ : (f g : Bits n → 𝔽) → (diag f ⊙ diag g) ≐ diag (λ x → f x * g x)
diag-⊙ f g x y = begin
  Σb (λ z → (f x * δb x z) * (g z * δb z y))
    ≡⟨ Σ-cong {f = λ z → (f x * δb x z) * (g z * δb z y)}
               {g = λ z → δb x z * (f x * (g z * δb z y))}
               (λ z → swapˡ (f x) (δb x z) (g z * δb z y)) ⟩
  Σb (λ z → δb x z * (f x * (g z * δb z y)))
    ≡⟨ Σ-δˡ x (λ z → f x * (g z * δb z y)) ⟩
  f x * (g x * δb x y)
    ≡⟨ Eq.sym (*-assoc (f x) (g x) (δb x y)) ⟩
  (f x * g x) * δb x y ∎
  where open Eq.≡-Reasoning

diag-comm : (f g : Bits n → 𝔽) → (diag f ⊙ diag g) ≐ (diag g ⊙ diag f)
diag-comm f g =
  ≐-trans (diag-⊙ f g)
    (≐-trans (diag-cong (λ x → *-comm (f x) (g x))) (≐-sym (diag-⊙ g f)))

-- Z on wire 0 is diagonal.
zph : Bits (₁₊ n) → 𝔽
zph (a ∷ _) = √2 * sgn a

private
  Z-emb : emb {1} {n} zM ≐ diag zph
  Z-emb (a ∷ x) (b ∷ y) = begin
    ix zM (a ∷ []) (b ∷ []) * δb x y
      ≡⟨ Eq.cong (_* δb x y) (entry a b) ⟩
    (√2 * sgn a) * δ₁ a b * δb x y
      ≡⟨ *-assoc (√2 * sgn a) (δ₁ a b) (δb x y) ⟩
    (√2 * sgn a) * (δ₁ a b * δb x y)
      ≡⟨ Eq.cong ((√2 * sgn a) *_) (Eq.sym (δb-∷ a b x y)) ⟩
    (√2 * sgn a) * δb (a ∷ x) (b ∷ y) ∎
    where
    open Eq.≡-Reasoning
    entry : ∀ a b → ix zM (a ∷ []) (b ∷ []) ≡ (√2 * sgn a) * δ₁ a b
    entry true  true  = Eq.refl
    entry true  false = Eq.refl
    entry false true  = Eq.refl
    entry false false = Eq.refl

-- The operator reading is abstract: Z is its gate, which is diagonal.
Z-diag : ⟦_⟧ₒ {₁₊ n} (Z ↓) ≐ diag zph
Z-diag = ≐-trans (⟦⟧ₒ-gen Z-gen) Z-emb

------------------------------------------------------------------------
-- Shifting and scaling diagonal operators

up-· : (c : 𝔽) (M : Op n) → up (c · M) ≐ (c · up M)
up-· c M (a ∷ x) (b ∷ y) = swapᵐ (δb (a ∷ []) (b ∷ [])) c (M x y)

-- The phase of a shifted diagonal operator ignores the new wire.
tl : (Bits n → 𝔽) → Bits (₁₊ n) → 𝔽
tl f (_ ∷ x) = f x

up-diag : (f : Bits n → 𝔽) → up (diag f) ≐ diag (tl f)
up-diag f (a ∷ x) (b ∷ y) = begin
  δb (a ∷ []) (b ∷ []) * (f x * δb x y)
    ≡⟨ Eq.cong (_* (f x * δb x y)) (Eq.trans (δb-∷ a b [] []) (*-identityʳ (δ₁ a b))) ⟩
  δ₁ a b * (f x * δb x y)
    ≡⟨ swapᵐ (δ₁ a b) (f x) (δb x y) ⟩
  f x * (δ₁ a b * δb x y)
    ≡⟨ Eq.cong (f x *_) (Eq.sym (δb-∷ a b x y)) ⟩
  f x * δb (a ∷ x) (b ∷ y) ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The transposition of wires 0 and 2

-- On bit vectors, and as a permutation operator.
sw : Bits (₃₊ n) → Bits (₃₊ n)
sw (a ∷ b ∷ c ∷ x) = c ∷ b ∷ a ∷ x

permOp : Op (₃₊ n)
permOp x y = δb (sw x) y

-- Its stored matrix on three wires.
permM : Mat 3
permM = matOf (λ x y → δb (sw x) y)

emb-perm : emb {3} {n} permM ≐ permOp
emb-perm (a ∷ b ∷ c ∷ x) (a' ∷ b' ∷ c' ∷ y) =
  Eq.trans (Eq.cong (_* δb x y) (ix-matOf (λ u v → δb (sw u) v) (a ∷ b ∷ c ∷ []) (a' ∷ b' ∷ c' ∷ [])))
           (Eq.sym (δb-₃ c b a a' b' c' x y))

-- Moving the transposition across the delta.
sw-δ : ∀ (x y : Bits (₃₊ n)) → δb (sw x) y ≡ δb x (sw y)
sw-δ (a ∷ b ∷ c ∷ x) (a' ∷ b' ∷ c' ∷ y) = begin
  δb (c ∷ b ∷ a ∷ x) (a' ∷ b' ∷ c' ∷ y)
    ≡⟨ Eq.trans (δb-∷ c a' _ _)
        (Eq.cong (δ₁ c a' *_) (Eq.trans (δb-∷ b b' _ _)
          (Eq.cong (δ₁ b b' *_) (δb-∷ a c' x y)))) ⟩
  δ₁ c a' * (δ₁ b b' * (δ₁ a c' * δb x y))
    ≡⟨ Eq.trans (Eq.sym (*-assoc _ _ _))
        (Eq.trans (Eq.cong (_* (δ₁ a c' * δb x y)) (*-comm (δ₁ c a') (δ₁ b b')))
          (Eq.trans (*-assoc _ _ _)
            (Eq.trans (Eq.cong (δ₁ b b' *_) (swapᵐ (δ₁ c a') (δ₁ a c') (δb x y)))
              (Eq.trans (Eq.sym (*-assoc _ _ _))
                (Eq.trans (Eq.cong (_* (δ₁ c a' * δb x y)) (*-comm (δ₁ b b') (δ₁ a c')))
                          (*-assoc _ _ _)))))) ⟩
  δ₁ a c' * (δ₁ b b' * (δ₁ c a' * δb x y))
    ≡⟨ Eq.sym (Eq.trans (δb-∷ a c' _ _)
        (Eq.cong (δ₁ a c' *_) (Eq.trans (δb-∷ b b' _ _)
          (Eq.cong (δ₁ b b' *_) (δb-∷ c a' x y))))) ⟩
  δb (a ∷ b ∷ c ∷ x) (c' ∷ b' ∷ a' ∷ y) ∎
  where open Eq.≡-Reasoning

sw-sw : ∀ (x : Bits (₃₊ n)) → sw (sw x) ≡ x
sw-sw (a ∷ b ∷ c ∷ x) = Eq.refl

-- Conjugating a diagonal operator by the transposition relabels its
-- phase.
perm-conj : (g : Bits (₃₊ n) → 𝔽) →
            (permOp ⊙ (diag g ⊙ permOp)) ≐ diag (λ x → g (sw x))
perm-conj g = ≐-trans (⊙-cong (≐-refl permOp) inner) outer
  where
  inner : (diag g ⊙ permOp) ≐ (λ x y → g x * δb x (sw y))
  inner x y = begin
    Σb (λ z → (g x * δb x z) * δb (sw z) y)
      ≡⟨ Σ-cong {f = λ z → (g x * δb x z) * δb (sw z) y}
                 {g = λ z → δb x z * (g x * δb z (sw y))}
                 (λ z → Eq.trans (Eq.cong ((g x * δb x z) *_) (sw-δ z y))
                                 (swapˡ (g x) (δb x z) (δb z (sw y)))) ⟩
    Σb (λ z → δb x z * (g x * δb z (sw y)))
      ≡⟨ Σ-δˡ x (λ z → g x * δb z (sw y)) ⟩
    g x * δb x (sw y) ∎
    where open Eq.≡-Reasoning
  outer : (permOp ⊙ (λ x y → g x * δb x (sw y))) ≐ diag (λ x → g (sw x))
  outer x y = begin
    Σb (λ z → δb (sw x) z * (g z * δb z (sw y)))
      ≡⟨ Σ-δˡ (sw x) (λ z → g z * δb z (sw y)) ⟩
    g (sw x) * δb (sw x) (sw y)
      ≡⟨ Eq.cong (g (sw x) *_) (Eq.trans (Eq.sym (sw-δ (sw x) y))
                                          (Eq.cong (λ □ → δb □ y) (sw-sw x))) ⟩
    g (sw x) * δb x y ∎
    where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Controlled operators
--
-- ctrl A B p acts as A on the bottom j wires when the predicate p holds
-- of the top ones, and as B otherwise.  It is defined by peeling bits
-- like the Kronecker product, and satisfies the same mixed product law.

ctrl : Op j → Op j → (Bits m → Bool) → Op (j +ℕ m)
ctrl {₀}    A B p u       v       = (if p u then A [] [] else B [] []) * δb u v
ctrl {₁₊ j} A B p (a ∷ x) (b ∷ y) =
  ctrl (λ u v → A (a ∷ u) (b ∷ v)) (λ u v → B (a ∷ u) (b ∷ v)) p x y

private
  if-same : ∀ (b : Bool) {x : 𝔽} → (if b then x else x) ≡ x
  if-same true  = Eq.refl
  if-same false = Eq.refl

  if-add : ∀ (b : Bool) (x x' y y' : 𝔽) →
           (if b then x + x' else y + y') ≡ (if b then x else y) + (if b then x' else y')
  if-add true  x x' y y' = Eq.refl
  if-add false x x' y y' = Eq.refl

  if-mul : ∀ (b : Bool) (x x' y y' d : 𝔽) →
           (if b then x else y) * ((if b then x' else y') * d) ≡
           (if b then x * x' else y * y') * d
  if-mul true  x x' y y' d = Eq.sym (*-assoc x x' d)
  if-mul false x x' y y' d = Eq.sym (*-assoc y y' d)

  if-scale : ∀ (b : Bool) (c x y : 𝔽) →
             (if b then c * x else c * y) ≡ c * (if b then x else y)
  if-scale true  c x y = Eq.refl
  if-scale false c x y = Eq.refl

ctrl-cong : {A A' B B' : Op j} {p : Bits m → Bool} →
            A ≐ A' → B ≐ B' → ctrl A B p ≐ ctrl A' B' p
ctrl-cong {₀} {p = p} e f u v =
  Eq.cong₂ (λ a b → (if p u then a else b) * δb u v) (e [] []) (f [] [])
ctrl-cong {₁₊ j} {m} {A} {A'} {B} {B'} e f (a ∷ x) (b ∷ y) =
  ctrl-cong {j} {m} {λ u v → A (a ∷ u) (b ∷ v)} {λ u v → A' (a ∷ u) (b ∷ v)}
                    {λ u v → B (a ∷ u) (b ∷ v)} {λ u v → B' (a ∷ u) (b ∷ v)}
            (λ u v → e (a ∷ u) (b ∷ v)) (λ u v → f (a ∷ u) (b ∷ v)) x y

ctrl-addˡ : (A A₂ B B₂ : Op j) (p : Bits m → Bool) → ∀ x y →
            ctrl (λ u v → A u v + A₂ u v) (λ u v → B u v + B₂ u v) p x y ≡
            ctrl A B p x y + ctrl A₂ B₂ p x y
ctrl-addˡ {₀} A A₂ B B₂ p u v =
  Eq.trans (Eq.cong (_* δb u v) (if-add (p u) _ _ _ _))
           (*-distribʳ-+ (δb u v) _ _)
ctrl-addˡ {₁₊ j} A A₂ B B₂ p (a ∷ x) (b ∷ y) =
  ctrl-addˡ {j} (λ u v → A (a ∷ u) (b ∷ v)) (λ u v → A₂ (a ∷ u) (b ∷ v))
                (λ u v → B (a ∷ u) (b ∷ v)) (λ u v → B₂ (a ∷ u) (b ∷ v)) p x y

-- The mixed product law for controlled operators.
ctrl-⊙ : (A A' B B' : Op j) (p : Bits m → Bool) →
         (ctrl A B p ⊙ ctrl A' B' p) ≐ ctrl (A ⊙ A') (B ⊙ B') p
ctrl-⊙ {₀} A A' B B' p u v = begin
  Σb (λ w → ((if p u then A [] [] else B [] []) * δb u w) *
            ((if p w then A' [] [] else B' [] []) * δb w v))
    ≡⟨ Σ-cong {f = λ w → ((if p u then A [] [] else B [] []) * δb u w) *
                         ((if p w then A' [] [] else B' [] []) * δb w v)}
               {g = λ w → δb u w * ((if p u then A [] [] else B [] []) *
                         ((if p w then A' [] [] else B' [] []) * δb w v))}
               (λ w → swapˡ _ (δb u w) _) ⟩
  Σb (λ w → δb u w * ((if p u then A [] [] else B [] []) *
                      ((if p w then A' [] [] else B' [] []) * δb w v)))
    ≡⟨ Σ-δˡ u (λ w → (if p u then A [] [] else B [] []) *
                      ((if p w then A' [] [] else B' [] []) * δb w v)) ⟩
  (if p u then A [] [] else B [] []) * ((if p u then A' [] [] else B' [] []) * δb u v)
    ≡⟨ if-mul (p u) _ _ _ _ (δb u v) ⟩
  (if p u then A [] [] * A' [] [] else B [] [] * B' [] []) * δb u v ∎
  where open Eq.≡-Reasoning
ctrl-⊙ {₁₊ j} {m} A A' B B' p (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong₂ _+_
             (ctrl-⊙ {j} {m} (λ u v → A (a ∷ u) (false ∷ v)) (λ u v → A' (false ∷ u) (b ∷ v))
                             (λ u v → B (a ∷ u) (false ∷ v)) (λ u v → B' (false ∷ u) (b ∷ v)) p x y)
             (ctrl-⊙ {j} {m} (λ u v → A (a ∷ u) (true ∷ v)) (λ u v → A' (true ∷ u) (b ∷ v))
                             (λ u v → B (a ∷ u) (true ∷ v)) (λ u v → B' (true ∷ u) (b ∷ v)) p x y))
           (Eq.sym (ctrl-addˡ {j}
                      (λ u v → Σb (λ w → A (a ∷ u) (false ∷ w) * A' (false ∷ w) (b ∷ v)))
                      (λ u v → Σb (λ w → A (a ∷ u) (true ∷ w) * A' (true ∷ w) (b ∷ v)))
                      (λ u v → Σb (λ w → B (a ∷ u) (false ∷ w) * B' (false ∷ w) (b ∷ v)))
                      (λ u v → Σb (λ w → B (a ∷ u) (true ∷ w) * B' (true ∷ w) (b ∷ v)))
                      p x y))

-- A local gate is a controlled operator with the same gate on both
-- branches, whatever the predicate.
tensor-ctrl : (M : Op j) (p : Bits m → Bool) → tensor M Idₒ ≐ ctrl M M p
tensor-ctrl {₀}    M p u       v       = Eq.cong (_* δb u v) (Eq.sym (if-same (p u)))
tensor-ctrl {₁₊ j} M p (a ∷ x) (b ∷ y) = tensor-ctrl {j} (λ u v → M (a ∷ u) (b ∷ v)) p x y

emb-ctrl : (C : Mat j) (p : Bits m → Bool) → emb {j} {m} C ≐ ctrl (ix C) (ix C) p
emb-ctrl C p = tensor-ctrl (ix C) p

-- A scalar passes out of both branches.
ctrl-· : (c : 𝔽) (A B : Op j) (p : Bits m → Bool) →
         ctrl (c · A) (c · B) p ≐ (c · ctrl A B p)
ctrl-· {₀}    c A B p u       v       =
  Eq.trans (Eq.cong (_* δb u v) (if-scale (p u) c _ _)) (*-assoc c _ (δb u v))
ctrl-· {₁₊ j} c A B p (a ∷ x) (b ∷ y) =
  ctrl-· {j} c (λ u v → A (a ∷ u) (b ∷ v)) (λ u v → B (a ∷ u) (b ∷ v)) p x y

-- A diagonal phase on three wires, controlled by the top ones, is the
-- diagonal operator that applies the phase when the control holds.
ctrlPhase : (Bits 3 → 𝔽) → (Bits m → Bool) → Bits (₃₊ m) → 𝔽
ctrlPhase g p (a ∷ b ∷ c ∷ u) = if p u then g (a ∷ b ∷ c ∷ []) else 1#

ctrl-diag : (g : Bits 3 → 𝔽) (p : Bits m → Bool) →
            ctrl (diag g) Idₒ p ≐ diag (ctrlPhase g p)
ctrl-diag g p (a ∷ b ∷ c ∷ u) (a' ∷ b' ∷ c' ∷ v) with p u
... | true  = Eq.trans (*-assoc (g (a ∷ b ∷ c ∷ [])) _ (δb u v))
                       (Eq.cong (g (a ∷ b ∷ c ∷ []) *_) (Eq.sym (δb-₃ a b c a' b' c' u v)))
... | false = Eq.trans (Eq.sym (δb-₃ a b c a' b' c' u v))
                       (Eq.sym (*-identityˡ (δb (a ∷ b ∷ c ∷ u) (a' ∷ b' ∷ c' ∷ v))))
