------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear coset tower: what the representatives compute
--
-- The fan-in R w adds the linear form w · x to wire 0 (R-at), the
-- fan-out col v adds multiples of wire 0 to the others (col-at), and
-- the row representative r ℓ writes the linear form ℓ · x on wire 0
-- (r-head); all three pick up no phase.  The data are read back from
-- these values: a linear form determines its row (dot-injective), and
-- rows that agree have the same representative (row-r) — the units
-- in them differ at most in their irrelevant nonvanishing proofs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

import Examples.Groups.Qupit-Phase-Affine.Soundness as Snd

module Examples.Groups.Qupit-Phase-Affine.Linear.Semantics
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ)
  (adm : Snd.Admissible p-2 p-prime lv) where

import Data.Integer.Base as ℤ
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime lv
  using (•-at ; ↑-at ; at-≡ ; SWAP-at ; M-at ; CXᶠ-at)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv using (ax)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime lv adm
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (sCX)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; conjᶠ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Linear forms and fan-outs on labels

dot : Vec F n → Labels n → F
dot []      []      = 0F
dot (c ∷ w) (a ∷ x) = c * a + dot w x

-- xᵢ + vᵢ a.
addv : F → Vec F n → Labels n → Labels n
addv a []      []      = []
addv a (c ∷ v) (b ∷ x) = b + c * a ∷ addv a v x

private
  zeros₃ : 0F + ((0F + 0F) + 0F) ≡ 0F
  zeros₃ = solve 0 (con (ℤ.+ 0) :+ ((con (ℤ.+ 0) :+ con (ℤ.+ 0)) :+ con (ℤ.+ 0)) := con (ℤ.+ 0)) refl

  zeros₂ : (0F + 0F) + 0F ≡ 0F
  zeros₂ = solve 0 ((con (ℤ.+ 0) :+ con (ℤ.+ 0)) :+ con (ℤ.+ 0) := con (ℤ.+ 0)) refl

------------------------------------------------------------------------
-- The fans

R-at : (w : Vec F n) (a : F) (x : Labels n) → ⟦ R w ⟧ (a ∷ x) ≡ (a + dot w x ∷ x , 0F)
R-at []      a []      = at-≡ (⟦⟧-ε (a ∷ [])) (cong (_∷ []) (sym (FR.+-identityʳ a))) refl
R-at (c ∷ w) a (b ∷ x) =
  at-≡ (•-at (CXᶠ-at c a b x)
             (•-at (•-at (SWAP-at a' b x) (↑-at (R-at w a' x))) (SWAP-at b (a' + dot w x) x)))
       (cong (λ t → t ∷ b ∷ x) (FR.+-assoc a (c * b) (dot w x)))
       zeros₃
  where
  a' = a + c * b

CXʳᶠ-at : (c a b : F) (x : Labels n) → ⟦ CXʳ ^ᶠ c ⟧ (a ∷ b ∷ x) ≡ (a ∷ b + c * a ∷ x , 0F)
CXʳᶠ-at c a b x =
  trans (sound (Width.sym (conjᶠ (ax swap-order) sCX c)) (a ∷ b ∷ x))
    (at-≡ (•-at (•-at (SWAP-at a b x) (CXᶠ-at c b a x)) (SWAP-at (b + c * a) a x)) refl zeros₂)
  where open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv using (module Width)

col-at : (v : Vec F n) (a : F) (x : Labels n) → ⟦ col v ⟧ (a ∷ x) ≡ (a ∷ addv a v x , 0F)
col-at []      a []      = ⟦⟧-ε (a ∷ [])
col-at (c ∷ v) a (b ∷ x) =
  at-≡ (•-at (CXʳᶠ-at c a b x)
             (•-at (•-at (SWAP-at a b' x) (↑-at (col-at v a x))) (SWAP-at b' a (addv a v x))))
       refl zeros₃
  where
  b' = b + c * a

------------------------------------------------------------------------
-- The row representatives

private
  -- SWAP puts wire 1 on wire 0.
  swap-head : {m : ℕ} (a : F) (y : Labels (₁₊ m)) → head (fn SWAP (a ∷ y)) ≡ head y
  swap-head a (b ∷ t) = cong (λ q → head (proj₁ q)) (SWAP-at a b t)

  swap-ph : {m : ℕ} (a : F) (y : Labels (₁₊ m)) → ph SWAP (a ∷ y) ≡ 0F
  swap-ph a (b ∷ t) = cong proj₂ (SWAP-at a b t)

r-head : (ℓ : NZ (₁₊ n)) (x : Labels (₁₊ n)) → head (fn (r ℓ) x) ≡ dot (row ℓ) x
r-head (big a w) (x₀ ∷ x) =
  cong (λ q → head (proj₁ q)) (•-at (M-at (proj₁ a) (proj₂ a) x₀ x) (R-at w (proj₁ a * x₀) x))
r-head (small ℓ) (x₀ ∷ x) = begin
  head (fn (SWAP • r ℓ ↑) (x₀ ∷ x))          ≡⟨ cong head (fn-• SWAP (r ℓ ↑) (x₀ ∷ x)) ⟩
  head (fn SWAP (fn (r ℓ ↑) (x₀ ∷ x)))       ≡⟨ cong (λ y → head (fn SWAP y)) (fn-↑ (r ℓ) x₀ x) ⟩
  head (fn SWAP (x₀ ∷ fn (r ℓ) x))           ≡⟨ swap-head x₀ (fn (r ℓ) x) ⟩
  head (fn (r ℓ) x)                          ≡⟨ r-head ℓ x ⟩
  dot (row ℓ) x                              ≡⟨ sym (trans (cong (_+ dot (row ℓ) x) (FR.zeroˡ x₀)) (FR.+-identityˡ _)) ⟩
  0F * x₀ + dot (row ℓ) x                    ∎
  where open ≡-Reasoning

r-ph : (ℓ : NZ n) (x : Labels n) → ph (r ℓ) x ≡ 0F
r-ph (big a w) (x₀ ∷ x) =
  trans (cong proj₂ (•-at (M-at (proj₁ a) (proj₂ a) x₀ x) (R-at w (proj₁ a * x₀) x))) (FR.+-identityʳ 0F)
r-ph (small ℓ) (x₀ ∷ x) = begin
  ph (SWAP • r ℓ ↑) (x₀ ∷ x)                             ≡⟨ ph-• SWAP (r ℓ ↑) (x₀ ∷ x) ⟩
  ph (r ℓ ↑) (x₀ ∷ x) + ph SWAP (fn (r ℓ ↑) (x₀ ∷ x))    ≡⟨ cong₂ _+_ (trans (ph-↑ (r ℓ) x₀ x) (r-ph ℓ x))
                                                                     (trans (cong (ph SWAP) (fn-↑ (r ℓ) x₀ x))
                                                                            (swap-ph x₀ (fn (r ℓ) x))) ⟩
  0F + 0F                                                ≡⟨ FR.+-identityʳ 0F ⟩
  0F                                                     ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Reading the data back

dot-zero : (w : Vec F n) → dot w 0ᵛ ≡ 0F
dot-zero []      = refl
dot-zero (c ∷ w) = trans (cong₂ _+_ (FR.zeroʳ c) (dot-zero w)) (FR.+-identityʳ 0F)

dot-injective : (u u' : Vec F n) → (∀ x → dot u x ≡ dot u' x) → u ≡ u'
dot-injective []      []        e = refl
dot-injective (c ∷ w) (c' ∷ w') e = cong₂ _∷_ head-eq (dot-injective w w' tail-eq)
  where
  at-e : (d : F) (v : Vec F _) → dot (d ∷ v) (1F ∷ 0ᵛ) ≡ d
  at-e d v = trans (cong₂ _+_ (FR.*-identityʳ d) (dot-zero v)) (FR.+-identityʳ d)
  head-eq : c ≡ c'
  head-eq = trans (sym (at-e c w)) (trans (e (1F ∷ 0ᵛ)) (at-e c' w'))
  at-0 : (d : F) (v : Vec F _) (x : Labels _) → dot (d ∷ v) (0F ∷ x) ≡ dot v x
  at-0 d v x = trans (cong (_+ dot v x) (FR.zeroʳ d)) (FR.+-identityˡ _)
  tail-eq : ∀ x → dot w x ≡ dot w' x
  tail-eq x = trans (sym (at-0 c w x)) (trans (e (0F ∷ x)) (at-0 c' w' x))

-- Rows that agree have the same representative.
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv using (row-r) public

-- The fan-out at wire 0 equal to 0 and to 1.
addv-0 : (v : Vec F n) (x : Labels n) → addv 0F v x ≡ x
addv-0 []      []      = refl
addv-0 (c ∷ v) (b ∷ x) = cong₂ _∷_ (trans (cong (b +_) (FR.zeroʳ c)) (FR.+-identityʳ b)) (addv-0 v x)

addv-1 : (v : Vec F n) → addv 1F v 0ᵛ ≡ v
addv-1 []      = refl
addv-1 (c ∷ v) = cong₂ _∷_ (trans (cong (0F +_) (FR.*-identityʳ c)) (FR.+-identityˡ c)) (addv-1 v)
