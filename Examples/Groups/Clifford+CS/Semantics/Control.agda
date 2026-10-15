------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators controlled by the top wire
--
-- The controlled functor (Lambda) puts a circuit under a control on a
-- new top wire.  Its semantics is block-diagonal on that wire:
--
--     blk P M  =  |0⟩⟨0| ⊗ P  +  |1⟩⟨1| ⊗ M      (the top wire last),
--
-- defined, like Algebra.tensor, by peeling bits from wire 0 up, so that
-- it needs no index arithmetic and its laws are inductions mirroring
-- tensor's.  A scaled operator (ℓ , M), the matrix γ^(−ℓ) M, controlled
-- by the top wire is (ℓ , blk (γ^ℓ) M) (`ctrl`), or with the control
-- white (ℓ , blk M (γ^ℓ)) (`ctrl⁰`): both respect _~_ and products.
--
-- Two permutations of the top wires are what the functor's spellings
-- conjugate by: the exchange of the top two wires (`swapL`), which
-- carries an idle wire under the control (`blk-swapL`), and the
-- negation of the top wire (`flipL`), which exchanges the two blocks
-- (`blk-flipL`).  `perm-conj` turns conjugation by such a map into
-- re-indexing.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Semantics.Control where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁₊ ; ₂₊)

open import Examples.Groups.Clifford+CS.Semantics.Algebra
open import Examples.Groups.Clifford+CS.Semantics.Local
open import Examples.Groups.Clifford+CS.Semantics.Scaled

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Block-diagonal on the top wire

-- The entry of a 2 × 2 block-diagonal matrix diag(p , q).
sel : Bool → Bool → 𝔽 → 𝔽 → 𝔽
sel false false p q = p
sel true  true  p q = q
sel _     _     p q = 0#

-- P where the top wire is 0, M where it is 1.
blk : Op n → Op n → Op (₁₊ n)
blk {₀}    P M (a ∷ []) (b ∷ []) = sel a b (P [] []) (M [] [])
blk {₁₊ n} P M (a ∷ x)  (b ∷ y)  =
  blk (λ u v → P (a ∷ u) (b ∷ v)) (λ u v → M (a ∷ u) (b ∷ v)) x y

blk-cong : {P P′ M M′ : Op n} → P ≐ P′ → M ≐ M′ → blk P M ≐ blk P′ M′
blk-cong {₀}    e f (a ∷ []) (b ∷ []) = Eq.cong₂ (sel a b) (e [] []) (f [] [])
blk-cong {₁₊ n} e f (a ∷ x)  (b ∷ y)  =
  blk-cong {n} (λ u v → e (a ∷ u) (b ∷ v)) (λ u v → f (a ∷ u) (b ∷ v)) x y

-- A scalar factor passes through both blocks.
blk-scale : (c : 𝔽) (P M : Op n) → ∀ x y → blk (c · P) (c · M) x y ≡ c * blk P M x y
blk-scale {₀}    c P M (false ∷ []) (false ∷ []) = Eq.refl
blk-scale {₀}    c P M (true ∷ [])  (true ∷ [])  = Eq.refl
blk-scale {₀}    c P M (false ∷ []) (true ∷ [])  = Eq.sym (*-zeroʳ c)
blk-scale {₀}    c P M (true ∷ [])  (false ∷ []) = Eq.sym (*-zeroʳ c)
blk-scale {₁₊ n} c P M (a ∷ x)      (b ∷ y)      =
  blk-scale {n} c (λ u v → P (a ∷ u) (b ∷ v)) (λ u v → M (a ∷ u) (b ∷ v)) x y

blk-zero : ∀ (x y : Bits (₁₊ n)) → blk {n} (λ _ _ → 0#) (λ _ _ → 0#) x y ≡ 0#
blk-zero {₀}    (false ∷ []) (false ∷ []) = Eq.refl
blk-zero {₀}    (true ∷ [])  (true ∷ [])  = Eq.refl
blk-zero {₀}    (false ∷ []) (true ∷ [])  = Eq.refl
blk-zero {₀}    (true ∷ [])  (false ∷ []) = Eq.refl
blk-zero {₁₊ n} (a ∷ x)      (b ∷ y)      = blk-zero {n} x y

-- Both blocks are additive, which is the step case of the product law.
blk-add : (P P′ M M′ : Op n) → ∀ x y →
          blk (λ u v → P u v + P′ u v) (λ u v → M u v + M′ u v) x y ≡
          blk P M x y + blk P′ M′ x y
blk-add {₀}    P P′ M M′ (false ∷ []) (false ∷ []) = Eq.refl
blk-add {₀}    P P′ M M′ (true ∷ [])  (true ∷ [])  = Eq.refl
blk-add {₀}    P P′ M M′ (false ∷ []) (true ∷ [])  = Eq.sym (+-identityʳ 0#)
blk-add {₀}    P P′ M M′ (true ∷ [])  (false ∷ []) = Eq.sym (+-identityʳ 0#)
blk-add {₁₊ n} P P′ M M′ (a ∷ x)      (b ∷ y)      =
  blk-add {n} (λ u v → P (a ∷ u) (b ∷ v)) (λ u v → P′ (a ∷ u) (b ∷ v))
              (λ u v → M (a ∷ u) (b ∷ v)) (λ u v → M′ (a ∷ u) (b ∷ v)) x y

-- Products are taken block by block.
blk-⊙ : (P M Q N : Op n) → (blk P M ⊙ blk Q N) ≐ blk (P ⊙ Q) (M ⊙ N)
blk-⊙ {₀} P M Q N (false ∷ []) (false ∷ []) =
  Eq.trans (Eq.cong (P [] [] * Q [] [] +_) (*-zeroˡ 0#)) (+-identityʳ _)
blk-⊙ {₀} P M Q N (true ∷ [])  (true ∷ [])  =
  Eq.trans (Eq.cong (_+ M [] [] * N [] []) (*-zeroˡ 0#)) (+-identityˡ _)
blk-⊙ {₀} P M Q N (false ∷ []) (true ∷ [])  =
  Eq.trans (Eq.cong₂ _+_ (*-zeroʳ (P [] [])) (*-zeroˡ (N [] []))) (+-identityʳ 0#)
blk-⊙ {₀} P M Q N (true ∷ [])  (false ∷ []) =
  Eq.trans (Eq.cong₂ _+_ (*-zeroˡ (Q [] [])) (*-zeroʳ (M [] []))) (+-identityʳ 0#)
blk-⊙ {₁₊ n} P M Q N (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong₂ _+_
             (blk-⊙ {n} (λ u v → P (a ∷ u) (false ∷ v)) (λ u v → M (a ∷ u) (false ∷ v))
                        (λ u v → Q (false ∷ u) (b ∷ v)) (λ u v → N (false ∷ u) (b ∷ v)) x y)
             (blk-⊙ {n} (λ u v → P (a ∷ u) (true ∷ v)) (λ u v → M (a ∷ u) (true ∷ v))
                        (λ u v → Q (true ∷ u) (b ∷ v)) (λ u v → N (true ∷ u) (b ∷ v)) x y))
           (Eq.sym (blk-add {n}
              (λ u v → Σb (λ w → P (a ∷ u) (false ∷ w) * Q (false ∷ w) (b ∷ v)))
              (λ u v → Σb (λ w → P (a ∷ u) (true ∷ w) * Q (true ∷ w) (b ∷ v)))
              (λ u v → Σb (λ w → M (a ∷ u) (false ∷ w) * N (false ∷ w) (b ∷ v)))
              (λ u v → Σb (λ w → M (a ∷ u) (true ∷ w) * N (true ∷ w) (b ∷ v))) x y))

blk-Id : blk {n} Idₒ Idₒ ≐ Idₒ
blk-Id {₀}    (false ∷ []) (false ∷ []) = Eq.refl
blk-Id {₀}    (true ∷ [])  (true ∷ [])  = Eq.refl
blk-Id {₀}    (false ∷ []) (true ∷ [])  = Eq.refl
blk-Id {₀}    (true ∷ [])  (false ∷ []) = Eq.refl
blk-Id {₁₊ n} (true ∷ x)   (true ∷ y)   = blk-Id {n} x y
blk-Id {₁₊ n} (false ∷ x)  (false ∷ y)  = blk-Id {n} x y
blk-Id {₁₊ n} (true ∷ x)   (false ∷ y)  = blk-zero {n} x y
blk-Id {₁₊ n} (false ∷ x)  (true ∷ y)   = blk-zero {n} x y

-- A scalar on both blocks is the scalar.
blk-scal : (c : 𝔽) → blk {n} (scal c) (scal c) ≐ scal c
blk-scal c x y = Eq.trans (blk-scale c Idₒ Idₒ x y) (Eq.cong (c *_) (blk-Id x y))

------------------------------------------------------------------------
-- The block form under the shift and the Kronecker product

-- An idle wire at the bottom passes into both blocks.
up-blk : (P M : Op n) → up (blk P M) ≐ blk (up P) (up M)
up-blk P M (a ∷ x) (b ∷ y) = Eq.sym (blk-scale (δb (a ∷ []) (b ∷ [])) P M x y)

-- A one- or two-wire factor at the bottom passes into both blocks.
blk-tensor₁ : (A : Op 1) (N N′ : Op m) → blk (tensor A N) (tensor A N′) ≐ tensor A (blk N N′)
blk-tensor₁ A N N′ (a ∷ x) (b ∷ y) = blk-scale (A (a ∷ []) (b ∷ [])) N N′ x y

blk-tensor₂ : (A : Op 2) (N N′ : Op m) → blk (tensor A N) (tensor A N′) ≐ tensor A (blk N N′)
blk-tensor₂ A N N′ (a ∷ a′ ∷ x) (b ∷ b′ ∷ y) =
  blk-scale (A (a ∷ a′ ∷ []) (b ∷ b′ ∷ [])) N N′ x y

------------------------------------------------------------------------
-- Permutations of bit vectors

-- The operator of a bit map π: |x⟩ ↦ |π x⟩ read as P x y = δ (π x) y.
permOp : (Bits n → Bits n) → Op n
permOp π x y = δb (π x) y

-- Conjugating by a self-inverse bit map re-indexes.
perm-conj : (π : Bits n → Bits n) → (∀ w y → δb (π w) y ≡ δb w (π y)) →
            (B : Op n) → ∀ x y → (permOp π ⊙ (B ⊙ permOp π)) x y ≡ B (π x) (π y)
perm-conj π inv B x y =
  Eq.trans (Σ-δˡ (π x) (λ z → (B ⊙ permOp π) z y))
    (Eq.trans (Σ-cong {f = λ w → B (π x) w * δb (π w) y} {g = λ w → B (π x) w * δb w (π y)}
                      (λ w → Eq.cong (B (π x) w *_) (inv w y)))
              (Σ-δʳ (π y) (λ w → B (π x) w)))

-- The shift of a permutation is the permutation fixing wire 0.
up-perm : (π : Bits n → Bits n) (σ : Bits (₁₊ n) → Bits (₁₊ n)) →
          (∀ a x → σ (a ∷ x) ≡ a ∷ π x) → up (permOp π) ≐ permOp σ
up-perm π σ e (a ∷ x) (b ∷ y) =
  Eq.trans (go a b) (Eq.cong (λ z → δb z (b ∷ y)) (Eq.sym (e a x)))
  where
  go : ∀ a b → δb (a ∷ []) (b ∷ []) * δb (π x) y ≡ δb (a ∷ π x) (b ∷ y)
  go true  true  = *-identityˡ (δb (π x) y)
  go false false = *-identityˡ (δb (π x) y)
  go true  false = *-zeroˡ (δb (π x) y)
  go false true  = *-zeroˡ (δb (π x) y)

-- The exchange of the top two wires.
swapL : Bits (₂₊ n) → Bits (₂₊ n)
swapL {₀}    (a ∷ b ∷ []) = b ∷ a ∷ []
swapL {₁₊ n} (a ∷ x)      = a ∷ swapL x

swapL-δ : ∀ (w y : Bits (₂₊ n)) → δb (swapL w) y ≡ δb w (swapL y)
swapL-δ {₀} (false ∷ false ∷ []) (false ∷ false ∷ []) = Eq.refl
swapL-δ {₀} (false ∷ false ∷ []) (false ∷ true ∷ [])  = Eq.refl
swapL-δ {₀} (false ∷ false ∷ []) (true ∷ false ∷ [])  = Eq.refl
swapL-δ {₀} (false ∷ false ∷ []) (true ∷ true ∷ [])   = Eq.refl
swapL-δ {₀} (false ∷ true ∷ [])  (false ∷ false ∷ []) = Eq.refl
swapL-δ {₀} (false ∷ true ∷ [])  (false ∷ true ∷ [])  = Eq.refl
swapL-δ {₀} (false ∷ true ∷ [])  (true ∷ false ∷ [])  = Eq.refl
swapL-δ {₀} (false ∷ true ∷ [])  (true ∷ true ∷ [])   = Eq.refl
swapL-δ {₀} (true ∷ false ∷ [])  (false ∷ false ∷ []) = Eq.refl
swapL-δ {₀} (true ∷ false ∷ [])  (false ∷ true ∷ [])  = Eq.refl
swapL-δ {₀} (true ∷ false ∷ [])  (true ∷ false ∷ [])  = Eq.refl
swapL-δ {₀} (true ∷ false ∷ [])  (true ∷ true ∷ [])   = Eq.refl
swapL-δ {₀} (true ∷ true ∷ [])   (false ∷ false ∷ []) = Eq.refl
swapL-δ {₀} (true ∷ true ∷ [])   (false ∷ true ∷ [])  = Eq.refl
swapL-δ {₀} (true ∷ true ∷ [])   (true ∷ false ∷ [])  = Eq.refl
swapL-δ {₀} (true ∷ true ∷ [])   (true ∷ true ∷ [])   = Eq.refl
swapL-δ {₁₊ n} (true ∷ w)  (true ∷ y)  = swapL-δ {n} w y
swapL-δ {₁₊ n} (false ∷ w) (false ∷ y) = swapL-δ {n} w y
swapL-δ {₁₊ n} (true ∷ w)  (false ∷ y) = Eq.refl
swapL-δ {₁₊ n} (false ∷ w) (true ∷ y)  = Eq.refl

-- The exchange carries an idle wire on top under the control below it.
blk-swapL : (P M : Op n) → ∀ x y →
            blk (blk P M) (blk P M) (swapL x) (swapL y) ≡ blk (blk P P) (blk M M) x y
blk-swapL {₀} P M (a ∷ b ∷ []) (c ∷ d ∷ []) = go a b c d
  where
  p = P [] []
  q = M [] []
  go : ∀ a b c d → sel a c (sel b d p q) (sel b d p q) ≡ sel b d (sel a c p p) (sel a c q q)
  go false false false false = Eq.refl
  go false false false true  = Eq.refl
  go false false true  false = Eq.refl
  go false false true  true  = Eq.refl
  go false true  false false = Eq.refl
  go false true  false true  = Eq.refl
  go false true  true  false = Eq.refl
  go false true  true  true  = Eq.refl
  go true  false false false = Eq.refl
  go true  false false true  = Eq.refl
  go true  false true  false = Eq.refl
  go true  false true  true  = Eq.refl
  go true  true  false false = Eq.refl
  go true  true  false true  = Eq.refl
  go true  true  true  false = Eq.refl
  go true  true  true  true  = Eq.refl
blk-swapL {₁₊ n} P M (e ∷ x) (f ∷ y) =
  blk-swapL {n} (λ u v → P (e ∷ u) (f ∷ v)) (λ u v → M (e ∷ u) (f ∷ v)) x y

-- The negation of the top wire.
flipL : Bits (₁₊ n) → Bits (₁₊ n)
flipL {₀}    (a ∷ []) = not a ∷ []
flipL {₁₊ n} (a ∷ x)  = a ∷ flipL x

flipL-δ : ∀ (w y : Bits (₁₊ n)) → δb (flipL w) y ≡ δb w (flipL y)
flipL-δ {₀} (false ∷ []) (false ∷ []) = Eq.refl
flipL-δ {₀} (false ∷ []) (true ∷ [])  = Eq.refl
flipL-δ {₀} (true ∷ [])  (false ∷ []) = Eq.refl
flipL-δ {₀} (true ∷ [])  (true ∷ [])  = Eq.refl
flipL-δ {₁₊ n} (true ∷ w)  (true ∷ y)  = flipL-δ {n} w y
flipL-δ {₁₊ n} (false ∷ w) (false ∷ y) = flipL-δ {n} w y
flipL-δ {₁₊ n} (true ∷ w)  (false ∷ y) = Eq.refl
flipL-δ {₁₊ n} (false ∷ w) (true ∷ y)  = Eq.refl

-- The negation exchanges the blocks.
blk-flipL : (P M : Op n) → ∀ x y → blk P M (flipL x) (flipL y) ≡ blk M P x y
blk-flipL {₀}    P M (false ∷ []) (false ∷ []) = Eq.refl
blk-flipL {₀}    P M (false ∷ []) (true ∷ [])  = Eq.refl
blk-flipL {₀}    P M (true ∷ [])  (false ∷ []) = Eq.refl
blk-flipL {₀}    P M (true ∷ [])  (true ∷ [])  = Eq.refl
blk-flipL {₁₊ n} P M (a ∷ x)      (b ∷ y)      =
  blk-flipL {n} (λ u v → P (a ∷ u) (b ∷ v)) (λ u v → M (a ∷ u) (b ∷ v)) x y

------------------------------------------------------------------------
-- Scaled operators under a control

ctrl ctrl⁰ : Scaled n → Scaled (₁₊ n)
ctrl  (l , M) = l , blk (scal (γ^ l)) M
ctrl⁰ (l , M) = l , blk M (scal (γ^ l))

private
  swapᵐ : ∀ (a b c : 𝔽) → a * (b * c) ≡ b * (a * c)
  swapᵐ a b c = Eq.trans (Eq.sym (*-assoc a b c))
    (Eq.trans (Eq.cong (_* c) (*-comm a b)) (*-assoc b a c))

  scal-cong : {c d : 𝔽} → c ≡ d → scal {n} c ≐ scal d
  scal-cong e x y = Eq.cong (_* δb x y) e

  -- γ^l′ · scal (γ^l) is symmetric in l and l′.
  ·-scal : (l l′ : ℕ) → (γ^ l′ · scal {n} (γ^ l)) ≐ (γ^ l · scal (γ^ l′))
  ·-scal l l′ x y = swapᵐ (γ^ l′) (γ^ l) (δb x y)

  scal-+ : (l l′ : ℕ) → (scal {n} (γ^ l) ⊙ scal (γ^ l′)) ≐ scal (γ^ (l +ℕ l′))
  scal-+ l l′ = ≐-trans (scal-⊙ (γ^ l) (γ^ l′)) (scal-cong (Eq.sym (γ^-+ l l′)))

ctrl-~ : {s t : Scaled n} → s ~ t → ctrl s ~ ctrl t
ctrl-~ {s = l , M} {l′ , M′} e x y =
  Eq.trans (Eq.sym (blk-scale (γ^ l′) (scal (γ^ l)) M x y))
    (Eq.trans (blk-cong (·-scal l l′) e x y)
              (blk-scale (γ^ l) (scal (γ^ l′)) M′ x y))

ctrl⁰-~ : {s t : Scaled n} → s ~ t → ctrl⁰ s ~ ctrl⁰ t
ctrl⁰-~ {s = l , M} {l′ , M′} e x y =
  Eq.trans (Eq.sym (blk-scale (γ^ l′) M (scal (γ^ l)) x y))
    (Eq.trans (blk-cong e (·-scal l l′) x y)
              (blk-scale (γ^ l) M′ (scal (γ^ l′)) x y))

ctrl-∙ : (s t : Scaled n) → ctrl (s ∙ t) ~ (ctrl s ∙ ctrl t)
ctrl-∙ (l , M) (l′ , N) =
  ~-reflexive {l = l +ℕ l′} {l +ℕ l′} Eq.refl
    (≐-sym (≐-trans (blk-⊙ (scal (γ^ l)) M (scal (γ^ l′)) N)
                    (blk-cong (scal-+ l l′) (≐-refl (M ⊙ N)))))

ctrl⁰-∙ : (s t : Scaled n) → ctrl⁰ (s ∙ t) ~ (ctrl⁰ s ∙ ctrl⁰ t)
ctrl⁰-∙ (l , M) (l′ , N) =
  ~-reflexive {l = l +ℕ l′} {l +ℕ l′} Eq.refl
    (≐-sym (≐-trans (blk-⊙ M (scal (γ^ l)) N (scal (γ^ l′)))
                    (blk-cong (≐-refl (M ⊙ N)) (scal-+ l l′))))

ctrl-ε : ctrl (ε∙ {n}) ~ ε∙
ctrl-ε = ~-reflexive {l = 0} {0} Eq.refl (≐-trans (blk-cong scal-1 (≐-refl Idₒ)) blk-Id)

ctrl⁰-ε : ctrl⁰ (ε∙ {n}) ~ ε∙
ctrl⁰-ε = ~-reflexive {l = 0} {0} Eq.refl (≐-trans (blk-cong (≐-refl Idₒ) scal-1) blk-Id)

------------------------------------------------------------------------
-- The shift of scaled operators

upS : Scaled n → Scaled (₁₊ n)
upS (l , M) = l , up M

up-· : (c : 𝔽) (M : Op n) → up (c · M) ≐ (c · up M)
up-· c M (a ∷ x) (b ∷ y) = swapᵐ (δb (a ∷ []) (b ∷ [])) c (M x y)

upS-~ : {s t : Scaled n} → s ~ t → upS s ~ upS t
upS-~ {s = l , M} {l′ , M′} e =
  ≐-trans (≐-sym (up-· (γ^ l′) M))
    (≐-trans (up-cong e) (up-· (γ^ l) M′))

upS-ctrl : (s : Scaled n) → upS (ctrl s) ~ ctrl (upS s)
upS-ctrl (l , M) =
  ~-reflexive {l = l} {l} Eq.refl
    (≐-trans (up-blk (scal (γ^ l)) M) (blk-cong (up-scal (γ^ l)) (≐-refl (up M))))

upS-ctrl⁰ : (s : Scaled n) → upS (ctrl⁰ s) ~ ctrl⁰ (upS s)
upS-ctrl⁰ (l , M) =
  ~-reflexive {l = l} {l} Eq.refl
    (≐-trans (up-blk M (scal (γ^ l))) (blk-cong (≐-refl (up M)) (up-scal (γ^ l))))
