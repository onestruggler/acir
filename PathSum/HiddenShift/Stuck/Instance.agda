------------------------------------------------------------------------
-- Presentations of groups
--
-- The hidden shift instance on which figure 2's rules get stuck
--
-- The data of PathSum.HiddenShift.Stuck: m = 3 (n = 6 qubits), the
-- polynomial g = x₀x₁ + x₀x₂ + x₁x₂ of degree 2 (bool-g: its Boolean
-- function gᵇ, the majority of three bits), the shift s = 0, and the
-- values of the hidden shift circuit on |0⟩ in algebraic normal form
-- (PathSum.Polynomial.ANF): the phase over ½, hs-parity on |0⟩, is
-- evalᴿ pF₀ (parity-ANF), and the outputs, the third Hadamard layer,
-- are evalᴿ (pG₀ w) (out-ANF).  The 18 path variables are numbered as
-- the composite numbers them: the first layer's a₀ a₁ a₂ b₀ b₁ b₂, the
-- second's c₀ c₁ c₂ d₀ d₁ d₂, the third's e₀ e₁ e₂ h₀ h₁ h₂.  Also the
-- values the reduction ends at -- phase ½ endF and outputs endG over
-- the ten variables b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ h₁ h₂ -- and the computed
-- certificate that each of them occurs in an output (end-occurs).
-- dotᴿ, the inner product on normal forms, is not about the instance.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Stuck.Instance (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (_+_; _*_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Vec.Base using ([]; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift M₀ using (boolᴾ; boolᴾ-resp; none)
open import PathSum.HiddenShift.Sign M₀ using (odd-+; odd-[])
open import PathSum.HiddenShift.Simulation M₀ using
  (hs-parity; layer₁; layer₂; layer₃)
open import PathSum.HiddenShift.Stuck.Machine M₀ using (Occurs)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; dot; dot-cong; mm; dual; mm-resp; dual-resp)
open import PathSum.Polynomial using (Poly; x[_]; μ; _+ᴾ_; eval)
open import PathSum.Polynomial.ANF using
  (RM; 𝟘; evalᴿ; _⊕ᴿ_; _∧ᴿ_; eval-⊕ᴿ; eval-∧ᴿ)
  renaming (var to varᴿ; eval-var to eval-varᴿ; lit to litᴿ;
            eval-lit to eval-litᴿ)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ; eval-μᴾ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ)

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- The instance

-- g = x₀x₁ + x₀x₂ + x₁x₂, a polynomial with integer coefficients on
-- three bits, of degree 2.

private
  f0 f1 f2 : Fin 3
  f0 = zero
  f1 = suc zero
  f2 = suc (suc zero)

g : Poly 3 0
g = (μ x[ f0 ] *ᴾ μ x[ f1 ]) +ᴾ
    ((μ x[ f0 ] *ᴾ μ x[ f2 ]) +ᴾ (μ x[ f1 ] *ᴾ μ x[ f2 ]))

-- The shift is 0.

s : Assign 6
s = 0ᵃ

-- The Boolean function g denotes: the majority of three bits.

gᵇ : (Fin 3 → Bool) → Bool
gᵇ u = (u f0 ∧ u f1) xor ((u f0 ∧ u f2) xor (u f1 ∧ u f2))

private
  mul-bits : ∀ a b → [ a ]ᶻ * [ b ]ᶻ ≡ [ a ∧ b ]ᶻ
  mul-bits false false = refl
  mul-bits false true  = refl
  mul-bits true  false = refl
  mul-bits true  true  = refl

  eval-pair : (u : Fin 3 → Bool) (i j : Fin 3) →
              eval (μ x[ i ] *ᴾ μ x[ j ]) u none ≡ [ u i ∧ u j ]ᶻ
  eval-pair u i j = trans (eval-*ᴾ (μ x[ i ]) (μ x[ j ]) u none)
    (trans (cong₂ _*_ (eval-μᴾ x[ i ] u none) (eval-μᴾ x[ j ] u none))
           (mul-bits (u i) (u j)))

bool-g : ∀ u → boolᴾ g u ≡ gᵇ u
bool-g u = trans (cong odd (trans
  (eval-+ᴾ (μ x[ f0 ] *ᴾ μ x[ f1 ]) B u none)
  (cong₂ _+_ (eval-pair u f0 f1)
    (trans (eval-+ᴾ (μ x[ f0 ] *ᴾ μ x[ f2 ]) (μ x[ f1 ] *ᴾ μ x[ f2 ]) u none)
           (cong₂ _+_ (eval-pair u f0 f2) (eval-pair u f1 f2))))))
  (trans (odd-+ [ u f0 ∧ u f1 ]ᶻ ([ u f0 ∧ u f2 ]ᶻ + [ u f1 ∧ u f2 ]ᶻ))
    (cong₂ _xor_ (odd-[] (u f0 ∧ u f1))
      (trans (odd-+ [ u f0 ∧ u f2 ]ᶻ [ u f1 ∧ u f2 ]ᶻ)
             (cong₂ _xor_ (odd-[] (u f0 ∧ u f2)) (odd-[] (u f1 ∧ u f2))))))
  where
  B : Poly 3 0
  B = (μ x[ f0 ] *ᴾ μ x[ f2 ]) +ᴾ (μ x[ f1 ] *ᴾ μ x[ f2 ])


------------------------------------------------------------------------
-- The circuit's values in normal form

-- Inner products, g, and the two oracles' exponents, on normal forms.

dotᴿ : ∀ {j} → (Fin j → RM k) → (Fin j → RM k) → RM k
dotᴿ {j = zero}  u v = 𝟘
dotᴿ {j = suc j} u v =
  (u zero ∧ᴿ v zero) ⊕ᴿ dotᴿ (λ i → u (suc i)) (λ i → v (suc i))

eval-dotᴿ : ∀ {j} (u v : Fin j → RM k) (ρ : Fin k → Bool) →
            evalᴿ (dotᴿ u v) ρ ≡
            dot (λ i → evalᴿ (u i) ρ) (λ i → evalᴿ (v i) ρ)
eval-dotᴿ {j = zero}  u v ρ = refl
eval-dotᴿ {j = suc j} u v ρ = trans
  (eval-⊕ᴿ (u zero ∧ᴿ v zero) (dotᴿ (λ i → u (suc i)) (λ i → v (suc i))) ρ)
  (cong₂ _xor_ (eval-∧ᴿ (u zero) (v zero) ρ)
               (eval-dotᴿ (λ i → u (suc i)) (λ i → v (suc i)) ρ))

gᴿ : (Fin 3 → RM k) → RM k
gᴿ t = (t f0 ∧ᴿ t f1) ⊕ᴿ ((t f0 ∧ᴿ t f2) ⊕ᴿ (t f1 ∧ᴿ t f2))

eval-gᴿ : (t : Fin 3 → RM k) (ρ : Fin k → Bool) →
          evalᴿ (gᴿ t) ρ ≡ gᵇ (λ i → evalᴿ (t i) ρ)
eval-gᴿ t ρ = trans
  (eval-⊕ᴿ (t f0 ∧ᴿ t f1) ((t f0 ∧ᴿ t f2) ⊕ᴿ (t f1 ∧ᴿ t f2)) ρ)
  (cong₂ _xor_ (eval-∧ᴿ (t f0) (t f1) ρ)
    (trans (eval-⊕ᴿ (t f0 ∧ᴿ t f2) (t f1 ∧ᴿ t f2) ρ)
           (cong₂ _xor_ (eval-∧ᴿ (t f0) (t f2) ρ) (eval-∧ᴿ (t f1) (t f2) ρ))))

mmᴿ dualᴿ : (Fin 6 → RM k) → RM k
mmᴿ   u = gᴿ (λ i → u (i ↑ˡ 3)) ⊕ᴿ dotᴿ (λ i → u (i ↑ˡ 3)) (λ i → u (3 ↑ʳ i))
dualᴿ u = gᴿ (λ i → u (3 ↑ʳ i)) ⊕ᴿ dotᴿ (λ i → u (i ↑ˡ 3)) (λ i → u (3 ↑ʳ i))

eval-mmᴿ : (u : Fin 6 → RM k) (ρ : Fin k → Bool) →
           evalᴿ (mmᴿ u) ρ ≡ mm (boolᴾ g) (λ i → evalᴿ (u i) ρ)
eval-mmᴿ u ρ = trans
  (eval-⊕ᴿ (gᴿ (λ i → u (i ↑ˡ 3)))
           (dotᴿ (λ i → u (i ↑ˡ 3)) (λ i → u (3 ↑ʳ i))) ρ)
  (cong₂ _xor_
  (trans (eval-gᴿ (λ i → u (i ↑ˡ 3)) ρ)
         (sym (bool-g (λ i → evalᴿ (u (i ↑ˡ 3)) ρ))))
  (eval-dotᴿ (λ i → u (i ↑ˡ 3)) (λ i → u (3 ↑ʳ i)) ρ))

eval-dualᴿ : (u : Fin 6 → RM k) (ρ : Fin k → Bool) →
             evalᴿ (dualᴿ u) ρ ≡ dual (boolᴾ g) (λ i → evalᴿ (u i) ρ)
eval-dualᴿ u ρ = trans
  (eval-⊕ᴿ (gᴿ (λ i → u (3 ↑ʳ i)))
           (dotᴿ (λ i → u (i ↑ˡ 3)) (λ i → u (3 ↑ʳ i))) ρ)
  (cong₂ _xor_
  (trans (eval-gᴿ (λ i → u (3 ↑ʳ i)) ρ)
         (sym (bool-g (λ i → evalᴿ (u (3 ↑ʳ i)) ρ))))
  (eval-dotᴿ (λ i → u (i ↑ˡ 3)) (λ i → u (3 ↑ʳ i)) ρ))

-- The three Hadamard layers' variables.

L₁ L₂ L₃ : Fin 6 → RM 18
L₁ i = varᴿ ((((i ↑ˡ 0) ↑ˡ 6) ↑ˡ 0) ↑ˡ 6)
L₂ i = varᴿ ((((6 ℕ+ 0) ↑ʳ i) ↑ˡ 0) ↑ˡ 6)
L₃ i = varᴿ ((((6 ℕ+ 0) ℕ+ 6) ℕ+ 0) ↑ʳ i)

-- The phase on |0⟩ over ½, and the outputs: hs-parity and the third
-- layer, in normal form.

pF₀ : RM 18
pF₀ = (((dotᴿ (λ _ → 𝟘) L₁ ⊕ᴿ mmᴿ (λ i → L₁ i ⊕ᴿ litᴿ (s i))) ⊕ᴿ
        dotᴿ L₁ L₂) ⊕ᴿ dualᴿ L₂) ⊕ᴿ dotᴿ L₂ L₃

pG₀ : Fin 6 → RM 18
pG₀ = L₃

-- hs-parity on |0⟩, spelled out.

private
  Z₀ : Fin 6 → RM 18
  Z₀ _ = 𝟘

  U₀ : Fin 6 → RM 18
  U₀ i = L₁ i ⊕ᴿ litᴿ (s i)

  hsP : Assign 18 → Bool
  hsP Y = (((dot 0ᵃ (layer₁ 6 Y) xor mm (boolᴾ g) (layer₁ 6 Y ⊕ᵃ s)) xor
            dot (layer₁ 6 Y) (layer₂ 6 Y)) xor dual (boolᴾ g) (layer₂ 6 Y)) xor
          dot (layer₂ 6 Y) (layer₃ 6 Y)

  hsP-≡ : ∀ Y → hs-parity g s 0ᵃ Y ≡ hsP Y
  hsP-≡ Y = refl

  l₁ : ∀ Y i → evalᴿ (L₁ i) Y ≡ layer₁ 6 Y i
  l₁ Y i = eval-varᴿ _ Y

  l₂ : ∀ Y i → evalᴿ (L₂ i) Y ≡ layer₂ 6 Y i
  l₂ Y i = eval-varᴿ _ Y

  l₃ : ∀ Y i → evalᴿ (L₃ i) Y ≡ layer₃ 6 Y i
  l₃ Y i = eval-varᴿ _ Y

  pA : ∀ Y → evalᴿ (dotᴿ Z₀ L₁) Y ≡ dot 0ᵃ (layer₁ 6 Y)
  pA Y = trans (eval-dotᴿ Z₀ L₁ Y)
    (dot-cong {u = λ _ → false} {u′ = 0ᵃ} {v = λ i → evalᴿ (L₁ i) Y}
              {v′ = layer₁ 6 Y} (λ _ → refl) (l₁ Y))

  pB : ∀ Y → evalᴿ (mmᴿ U₀) Y ≡ mm (boolᴾ g) (layer₁ 6 Y ⊕ᵃ s)
  pB Y = trans (eval-mmᴿ U₀ Y)
    (mm-resp (boolᴾ g) (boolᴾ-resp g) (λ i → evalᴿ (U₀ i) Y)
             (layer₁ 6 Y ⊕ᵃ s) shifted)
    where
    shifted : ∀ i → evalᴿ (U₀ i) Y ≡ (layer₁ 6 Y ⊕ᵃ s) i
    shifted i = trans (eval-⊕ᴿ (L₁ i) (litᴿ (s i)) Y)
      (cong₂ _xor_ (l₁ Y i) (eval-litᴿ (s i) Y))

  pC : ∀ Y → evalᴿ (dotᴿ L₁ L₂) Y ≡ dot (layer₁ 6 Y) (layer₂ 6 Y)
  pC Y = trans (eval-dotᴿ L₁ L₂ Y)
    (dot-cong {u = λ i → evalᴿ (L₁ i) Y} {u′ = layer₁ 6 Y}
              {v = λ i → evalᴿ (L₂ i) Y} {v′ = layer₂ 6 Y} (l₁ Y) (l₂ Y))

  pD : ∀ Y → evalᴿ (dualᴿ L₂) Y ≡ dual (boolᴾ g) (layer₂ 6 Y)
  pD Y = trans (eval-dualᴿ L₂ Y)
    (dual-resp (boolᴾ g) (boolᴾ-resp g) (λ i → evalᴿ (L₂ i) Y)
               (layer₂ 6 Y) (l₂ Y))

  pE : ∀ Y → evalᴿ (dotᴿ L₂ L₃) Y ≡ dot (layer₂ 6 Y) (layer₃ 6 Y)
  pE Y = trans (eval-dotᴿ L₂ L₃ Y)
    (dot-cong {u = λ i → evalᴿ (L₂ i) Y} {u′ = layer₂ 6 Y}
              {v = λ i → evalᴿ (L₃ i) Y} {v′ = layer₃ 6 Y} (l₂ Y) (l₃ Y))

  F₁ F₂ F₃ F₄ : RM 18
  F₁ = dotᴿ Z₀ L₁ ⊕ᴿ mmᴿ U₀
  F₂ = F₁ ⊕ᴿ dotᴿ L₁ L₂
  F₃ = F₂ ⊕ᴿ dualᴿ L₂
  F₄ = F₃ ⊕ᴿ dotᴿ L₂ L₃

  F₄-≡ : pF₀ ≡ F₄
  F₄-≡ = refl

parity-ANF : ∀ Y → hs-parity g s 0ᵃ Y ≡ evalᴿ pF₀ Y
parity-ANF Y = trans (hsP-≡ Y) (sym (trans (cong (λ p → evalᴿ p Y) F₄-≡)
  (trans (eval-⊕ᴿ F₃ (dotᴿ L₂ L₃) Y) (cong₂ _xor_
    (trans (eval-⊕ᴿ F₂ (dualᴿ L₂) Y) (cong₂ _xor_
      (trans (eval-⊕ᴿ F₁ (dotᴿ L₁ L₂) Y) (cong₂ _xor_
        (trans (eval-⊕ᴿ (dotᴿ Z₀ L₁) (mmᴿ U₀) Y)
               (cong₂ _xor_ (pA Y) (pB Y)))
        (pC Y)))
      (pD Y)))
    (pE Y)))))

out-ANF : ∀ w Y → layer₃ 6 Y w ≡ evalᴿ (pG₀ w) Y
out-ANF w Y = sym (eval-varᴿ _ Y)




------------------------------------------------------------------------
-- The end of the reduction

-- The ten path variables left, in their order.

private
  b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ h₁ h₂ : RM 10
  b₁ = varᴿ (# 0)
  b₂ = varᴿ (# 1)
  c₁ = varᴿ (# 2)
  c₂ = varᴿ (# 3)
  d₁ = varᴿ (# 4)
  d₂ = varᴿ (# 5)
  e₁ = varᴿ (# 6)
  e₂ = varᴿ (# 7)
  h₁ = varᴿ (# 8)
  h₂ = varᴿ (# 9)

-- Its phase over ½ and its outputs, as the paper would write them.

endF : RM 10
endF = b₁ ∧ᴿ b₂ ⊕ᴿ b₂ ∧ᴿ c₁ ⊕ᴿ b₁ ∧ᴿ c₂ ⊕ᴿ c₁ ∧ᴿ c₂ ⊕ᴿ b₁ ∧ᴿ d₁ ⊕ᴿ
       c₁ ∧ᴿ d₁ ⊕ᴿ b₂ ∧ᴿ d₂ ⊕ᴿ c₂ ∧ᴿ d₂ ⊕ᴿ d₁ ∧ᴿ d₂ ⊕ᴿ c₁ ∧ᴿ e₁ ⊕ᴿ
       c₂ ∧ᴿ e₂ ⊕ᴿ d₁ ∧ᴿ h₁ ⊕ᴿ d₂ ∧ᴿ h₂

endG : Fin 6 → RM 10
endG w = lookup (𝟘 ∷ e₁ ∷ e₂ ∷
                 (litᴿ true ⊕ᴿ b₁ ⊕ᴿ b₂ ⊕ᴿ c₁ ⊕ᴿ c₂ ⊕ᴿ d₁ ⊕ᴿ d₂) ∷
                 h₁ ∷ h₂ ∷ []) w

-- Every variable occurs in an output.

end-occurs : Occurs endG ≡ true
end-occurs = refl
