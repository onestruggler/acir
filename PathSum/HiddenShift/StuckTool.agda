------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of figure 2 can get stuck on the tool's own hidden shift
-- circuit
--
-- PathSum.HiddenShift.Stuck shows that a maximal reduction of the
-- hidden shift circuit on |0⟩ can end with path variables left, at
-- m = 3 with a quadratic g.  The paper's tool cannot draw that g: its
-- Maiorana-McFarland functions (PathSum.HiddenShift.Tool) have a ccz
-- in every alternation, so a cubic monomial.  This module shows that
-- figure 2's rules get stuck on the tool's own circuit all the same
-- (PathSum.HiddenShift.Tool's HSᵗ, over {H, X, CNOT, R_k, R_k†} with X
-- primitive, as PathSum.HiddenShift.ToolExists reduces it): for n = 8
-- qubits, shift 0 and one alternation of the tool's size -- a ccz on
-- wires 1, 2, 3 and 200 draws, a cz on wires 0, 2, a cz on wires 0,
-- 1, then 198 Z on wire 0, which cancel in pairs -- the function is
-- g = x₁x₂x₃ + x₀x₂ + x₀x₁, and six [HH] steps, each followed by an
-- [Elim], reach a path-sum with twelve path variables to which no rule
-- applies (tool-stuck), while a complete reduction of it exists and
-- ends at |s⟩ (ToolExists' tool-finds).  So the qualification the
-- paper's sentence needs holds of the tool's own circuit family (here
-- n = 8 with one alternation, not table 2's sizes), via a non-linear
-- [HH] quotient; no stuck state under the linear rules alone was found
-- on tool-style circuits at m = 4 (a search outside Agda).
--
-- The chain, in the labels of PathSum.HiddenShift.Blocks:
--
--    [HH] at a₀, c₀ ← a₁ ⊕ a₂ ⊕ b₀       [HH] at c₃, e₃ ← 0
--    [HH] at b₀, e₀ ← 0                  [HH] at d₀, d₁ ← a₁ ⊕ a₂ ⊕ d₂ ⊕ h₀
--    [HH] at b₃, d₃ ← a₃                 [HH] at a₂, h₁ ← a₁a₃ ⊕ b₁ ⊕ b₂
--                                                       ⊕ c₁ ⊕ c₂ ⊕ a₃d₂
--
-- The last quotient is not linear: [HH] allows that -- its quotient is
-- any Boolean-valued Q, here the lift of that Boolean polynomial -- and
-- it substitutes it for the output variable h₁, after which every one
-- of the twelve remaining variables a₁ a₃ b₁ b₂ c₁ c₂ d₂ e₁ e₂ h₀ h₂ h₃
-- occurs in an output.  (With this g the search outside Agda found no
-- path-sum on which the linear rules alone get stuck, nor with a ccz
-- on wires 1, 2, 3 and any set of cz's at m = 4.)  The chain is built
-- by PathSum.HiddenShift.Stuck.Machine's step (PathSum.Full's _⟶ᶠ_,
-- through PathSum.HiddenShift.Track's hh-elim), numbered as the tool's
-- circuit numbers its 24 path variables, as definition 2.9 numbers
-- Hadamards (the third layer, the second, the first, wire w of each at
-- 7 - w: PathSum.HiddenShift.ThreeLayers' lay₁, lay₂, lay₃).  The
-- values are ToolExists' (along a path, the phase is ½ hs-par and the
-- outputs are the third layer; proved there privately and re-derived
-- here, for every size, from PathSum.HiddenShift.ToolRuns), and the
-- oracle's Boolean function is read off the drawn monomials in
-- algebraic normal form (sumᴿ), so the 201 monomials are summed, and
-- the pairs cancelled, by computation.
--
-- The draw is one the tool can make, not one it is likely to make;
-- nothing here is about the tool's random distribution.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.StuckTool (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Fin using (#_)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; opposite; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.Integer.Base using (0ℤ; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; replicate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CRK.Trace M₀ using (str; pathOf-str)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Gates M₀ using
  (Term; Z; CZ; CCZ; mono; sumᵇ; sumᵇ-resp)
open import PathSum.HiddenShift.Layout using (hs-par)
open import PathSum.HiddenShift.Simulation M₀ using (at0; eval-at0)
open import PathSum.HiddenShift.Stuck.Instance M₀ using (dotᴿ; eval-dotᴿ)
open import PathSum.HiddenShift.Stuck.Machine M₀ using
  (tracks-cong; module Reduce; Occurs; occurs⇒irreducible)
open import PathSum.HiddenShift.ThreeLayers M₀ using (lay₁; lay₂; lay₃)
open import PathSum.HiddenShift.Tool M₀ using
  (Block; block; Draw; CZᵈ; Zᵈ; gTerms; HSᵗ)
open import PathSum.HiddenShift.ToolRuns M₀ using (runs-HSᵗ)
open import PathSum.HiddenShift.TraceX M₀ using
  (traceˣ; eval-⟦⟧ˣ; outBit-⟦⟧ˣ; runsˣ-φ; runsˣ-v)
open import PathSum.HiddenShift.Track M₀ using (Tracks; phase-at; out-at)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; dot; dot-cong; mm; dual; mm-resp; dual-resp)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.ANF using
  (RM; 𝟘; evalᴿ; _⊕ᴿ_; _∧ᴿ_; eval-⊕ᴿ; eval-∧ᴿ; eqᴿ; eqᴿ-sound; allFin;
   allFin-sound)
  renaming (var to varᴿ; eval-var to eval-varᴿ; lit to litᴿ;
            eval-lit to eval-litᴿ)
open import PathSum.Polynomial.Bind using (odd)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.WithX M₀ using (norm; paths; ⟦_⟧)
open import PathSum.Full M using (_⟶ᶠ*_; εᶠ)
open import PathSum.Full.Match M using (Irreducibleᶠ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

private
  variable
    k m : ℕ


------------------------------------------------------------------------
-- Monomials in normal form

termᴿ : Term m → (Fin m → RM k) → RM k
termᴿ (Z a)             t = t a
termᴿ (CZ a b _)        t = t a ∧ᴿ t b
termᴿ (CCZ a b c _ _ _) t = t a ∧ᴿ (t b ∧ᴿ t c)

sumᴿ : List (Term m) → (Fin m → RM k) → RM k
sumᴿ []       t = 𝟘
sumᴿ (u ∷ us) t = termᴿ u t ⊕ᴿ sumᴿ us t

eval-termᴿ : (u : Term m) (t : Fin m → RM k) (ρ : Fin k → Bool) →
             evalᴿ (termᴿ u t) ρ ≡ mono u (λ i → evalᴿ (t i) ρ)
eval-termᴿ (Z a)             t ρ = refl
eval-termᴿ (CZ a b _)        t ρ = eval-∧ᴿ (t a) (t b) ρ
eval-termᴿ (CCZ a b c _ _ _) t ρ = trans (eval-∧ᴿ (t a) (t b ∧ᴿ t c) ρ)
  (cong (evalᴿ (t a) ρ ∧_) (eval-∧ᴿ (t b) (t c) ρ))

eval-sumᴿ : (us : List (Term m)) (t : Fin m → RM k) (ρ : Fin k → Bool) →
            evalᴿ (sumᴿ us t) ρ ≡ sumᵇ us (λ i → evalᴿ (t i) ρ)
eval-sumᴿ []       t ρ = refl
eval-sumᴿ (u ∷ us) t ρ = trans (eval-⊕ᴿ (termᴿ u t) (sumᴿ us t) ρ)
  (cong₂ _xor_ (eval-termᴿ u t ρ) (eval-sumᴿ us t ρ))


------------------------------------------------------------------------
-- The draw

private
  f0 f1 f2 f3 : Fin 4
  f0 = zero
  f1 = suc zero
  f2 = suc (suc zero)
  f3 = suc (suc (suc zero))

  0≢1 : f0 ≢ f1
  0≢1 ()

  0≢2 : f0 ≢ f2
  0≢2 ()

  1≢2 : f1 ≢ f2
  1≢2 ()

  1≢3 : f1 ≢ f3
  1≢3 ()

  2≢3 : f2 ≢ f3
  2≢3 ()

-- One alternation of the tool's size: the ccz on wires 1, 2, 3, then
-- 200 draws -- cz on 0, 2, cz on 0, 1 and 198 Z on 0.

draws : Vec (Draw 4) 200
draws = CZᵈ f0 f2 0≢2 ∷ CZᵈ f0 f1 0≢1 ∷ replicate 198 (Zᵈ f0)

Bs : List (Block 200 4)
Bs = block f1 f2 f3 1≢2 1≢3 2≢3 draws ∷ []

-- The shift is 0.

s : Assign 8
s = 0ᵃ


------------------------------------------------------------------------
-- The circuit's values in normal form

private
  gᵗ : (Fin 4 → Bool) → Bool
  gᵗ = sumᵇ (gTerms Bs)

  mmᴿ dualᴿ : (Fin 8 → RM k) → RM k
  mmᴿ u = sumᴿ (gTerms Bs) (λ i → u (i ↑ˡ 4)) ⊕ᴿ
          dotᴿ (λ i → u (i ↑ˡ 4)) (λ i → u (4 ↑ʳ i))
  dualᴿ u = sumᴿ (gTerms Bs) (λ i → u (4 ↑ʳ i)) ⊕ᴿ
            dotᴿ (λ i → u (i ↑ˡ 4)) (λ i → u (4 ↑ʳ i))

  eval-mmᴿ : (u : Fin 8 → RM k) (ρ : Fin k → Bool) →
             evalᴿ (mmᴿ u) ρ ≡ mm gᵗ (λ i → evalᴿ (u i) ρ)
  eval-mmᴿ u ρ = trans
    (eval-⊕ᴿ (sumᴿ (gTerms Bs) (λ i → u (i ↑ˡ 4)))
             (dotᴿ (λ i → u (i ↑ˡ 4)) (λ i → u (4 ↑ʳ i))) ρ)
    (cong₂ _xor_ (eval-sumᴿ (gTerms Bs) (λ i → u (i ↑ˡ 4)) ρ)
                 (eval-dotᴿ (λ i → u (i ↑ˡ 4)) (λ i → u (4 ↑ʳ i)) ρ))

  eval-dualᴿ : (u : Fin 8 → RM k) (ρ : Fin k → Bool) →
               evalᴿ (dualᴿ u) ρ ≡ dual gᵗ (λ i → evalᴿ (u i) ρ)
  eval-dualᴿ u ρ = trans
    (eval-⊕ᴿ (sumᴿ (gTerms Bs) (λ i → u (4 ↑ʳ i)))
             (dotᴿ (λ i → u (i ↑ˡ 4)) (λ i → u (4 ↑ʳ i))) ρ)
    (cong₂ _xor_ (eval-sumᴿ (gTerms Bs) (λ i → u (4 ↑ʳ i)) ρ)
                 (eval-dotᴿ (λ i → u (i ↑ˡ 4)) (λ i → u (4 ↑ʳ i)) ρ))

  -- The three layers' variables, numbered as definition 2.9 numbers
  -- the circuit's Hadamards: the third layer first, wire w at 7 - w.

  T₁ T₂ T₃ : Fin 8 → RM 24
  T₁ w = varᴿ (16 ↑ʳ opposite w)
  T₂ w = varᴿ (8 ↑ʳ (opposite w ↑ˡ 8))
  T₃ w = varᴿ (opposite w ↑ˡ 16)

  t₁ : ∀ y w → evalᴿ (T₁ w) y ≡ lay₁ 8 (str y) w
  t₁ y w = trans (eval-varᴿ _ y)
    (trans (sym (pathOf-str y (16 ↑ʳ opposite w)))
           (cong (str y) (toℕ-↑ʳ 16 (opposite w))))

  t₂ : ∀ y w → evalᴿ (T₂ w) y ≡ lay₂ 8 (str y) w
  t₂ y w = trans (eval-varᴿ _ y)
    (trans (sym (pathOf-str y (8 ↑ʳ (opposite w ↑ˡ 8))))
           (cong (str y) (trans (toℕ-↑ʳ 8 (opposite w ↑ˡ 8))
                                (cong (8 ℕ+_) (toℕ-↑ˡ (opposite w) 8)))))

  t₃ : ∀ y w → evalᴿ (T₃ w) y ≡ lay₃ 8 (str y) w
  t₃ y w = trans (eval-varᴿ _ y)
    (trans (sym (pathOf-str y (opposite w ↑ˡ 16)))
           (cong (str y) (toℕ-↑ˡ (opposite w) 16)))

  U₀ : Fin 8 → RM 24
  U₀ w = T₁ w ⊕ᴿ litᴿ (s w)

  F₁ F₂ F₃ : RM 24
  F₁ = mmᴿ U₀ ⊕ᴿ dotᴿ T₁ T₂
  F₂ = F₁ ⊕ᴿ dualᴿ T₂
  F₃ = F₂ ⊕ᴿ dotᴿ T₂ T₃

pFᵗ : RM 24
pFᵗ = ((mmᴿ U₀ ⊕ᴿ dotᴿ T₁ T₂) ⊕ᴿ dualᴿ T₂) ⊕ᴿ dotᴿ T₂ T₃

pGᵗ : Fin 8 → RM 24
pGᵗ = T₃

private
  l₁ : Assign 24 → Fin 8 → Bool
  l₁ y = lay₁ 8 (str y)

  l₂ : Assign 24 → Fin 8 → Bool
  l₂ y = lay₂ 8 (str y)

  l₃ : Assign 24 → Fin 8 → Bool
  l₃ y = lay₃ 8 (str y)

  hsP : Assign 24 → Bool
  hsP y = hs-par gᵗ s (l₁ y) (l₂ y) (l₃ y)

  pB : ∀ y → evalᴿ (mmᴿ U₀) y ≡ mm gᵗ (l₁ y ⊕ᵃ s)
  pB y = trans (eval-mmᴿ U₀ y)
    (mm-resp gᵗ (sumᵇ-resp (gTerms Bs)) (λ i → evalᴿ (U₀ i) y)
             (l₁ y ⊕ᵃ s) shifted)
    where
    shifted : ∀ i → evalᴿ (U₀ i) y ≡ (l₁ y ⊕ᵃ s) i
    shifted i = trans (eval-⊕ᴿ (T₁ i) (litᴿ (s i)) y)
      (cong₂ _xor_ (t₁ y i) (eval-litᴿ (s i) y))

  pC : ∀ y → evalᴿ (dotᴿ T₁ T₂) y ≡ dot (l₁ y) (l₂ y)
  pC y = trans (eval-dotᴿ T₁ T₂ y)
    (dot-cong {u = λ i → evalᴿ (T₁ i) y} {u′ = l₁ y}
              {v = λ i → evalᴿ (T₂ i) y} {v′ = l₂ y} (t₁ y) (t₂ y))

  pD : ∀ y → evalᴿ (dualᴿ T₂) y ≡ dual gᵗ (l₂ y)
  pD y = trans (eval-dualᴿ T₂ y)
    (dual-resp gᵗ (sumᵇ-resp (gTerms Bs)) (λ i → evalᴿ (T₂ i) y)
               (l₂ y) (t₂ y))

  pE : ∀ y → evalᴿ (dotᴿ T₂ T₃) y ≡ dot (l₂ y) (l₃ y)
  pE y = trans (eval-dotᴿ T₂ T₃ y)
    (dot-cong {u = λ i → evalᴿ (T₂ i) y} {u′ = l₂ y}
              {v = λ i → evalᴿ (T₃ i) y} {v′ = l₃ y} (t₂ y) (t₃ y))

  F₃-≡ : pFᵗ ≡ F₃
  F₃-≡ = refl

parity-ANFᵗ : ∀ y → hs-par (sumᵇ (gTerms Bs)) s (lay₁ 8 (str y))
                      (lay₂ 8 (str y)) (lay₃ 8 (str y)) ≡ evalᴿ pFᵗ y
parity-ANFᵗ y = sym (trans (cong (λ p → evalᴿ p y) F₃-≡)
  (trans (eval-⊕ᴿ F₂ (dotᴿ T₂ T₃) y) (cong₂ _xor_
    (trans (eval-⊕ᴿ F₁ (dualᴿ T₂) y) (cong₂ _xor_
      (trans (eval-⊕ᴿ (mmᴿ U₀) (dotᴿ T₁ T₂) y)
             (cong₂ _xor_ (pB y) (pC y)))
      (pD y)))
    (pE y))))

out-ANFᵗ : ∀ w y → lay₃ 8 (str y) w ≡ evalᴿ (pGᵗ w) y
out-ANFᵗ w y = sym (t₃ y w)


------------------------------------------------------------------------
-- The end, in the tool's numbering

private
  a₁ a₃ b₁ b₂ c₁ c₂ d₂ e₁ e₂ h₀ h₂ h₃ : RM 12
  h₃ = varᴿ (# 0)
  h₂ = varᴿ (# 1)
  h₀ = varᴿ (# 2)
  e₂ = varᴿ (# 3)
  e₁ = varᴿ (# 4)
  d₂ = varᴿ (# 5)
  c₂ = varᴿ (# 6)
  c₁ = varᴿ (# 7)
  b₂ = varᴿ (# 8)
  b₁ = varᴿ (# 9)
  a₃ = varᴿ (# 10)
  a₁ = varᴿ (# 11)

endFᵗ : RM 12
endFᵗ = a₁ ∧ᴿ a₃ ⊕ᴿ a₁ ∧ᴿ b₁ ⊕ᴿ a₁ ∧ᴿ b₂ ⊕ᴿ a₁ ∧ᴿ c₁ ⊕ᴿ a₁ ∧ᴿ c₂ ⊕ᴿ
        a₁ ∧ᴿ a₃ ∧ᴿ d₂ ⊕ᴿ c₁ ∧ᴿ e₁ ⊕ᴿ c₂ ∧ᴿ e₂ ⊕ᴿ a₁ ∧ᴿ a₃ ∧ᴿ h₀ ⊕ᴿ
        b₂ ∧ᴿ h₀ ⊕ᴿ c₂ ∧ᴿ h₀ ⊕ᴿ d₂ ∧ᴿ h₂ ⊕ᴿ a₃ ∧ᴿ h₃

endGᵗ : Fin 8 → RM 12
endGᵗ w = lookup (𝟘 ∷ e₁ ∷ e₂ ∷ 𝟘 ∷ h₀ ∷
                  (a₁ ∧ᴿ a₃ ⊕ᴿ b₁ ⊕ᴿ b₂ ⊕ᴿ c₁ ⊕ᴿ c₂ ⊕ᴿ a₃ ∧ᴿ d₂) ∷
                  h₂ ∷ h₃ ∷ []) w

end-occursᵗ : Occurs endGᵗ ≡ true
end-occursᵗ = refl


------------------------------------------------------------------------
-- The reduction

-- Along a path of the tool's circuit on |0⟩, the phase is ½ hs-par and
-- the outputs are the third layer (ToolExists' ph and ob, which are
-- private there).  Proved for every m, draw and shift, as there: at a
-- numeral size the conversion between an output and its parity would
-- unfold every monomial.

module _ {m d : ℕ} (s′ : Assign (m ℕ+ m)) (Bs′ : List (Block d m)) where

  tool-tracks :
    Tracks (at0 ⟦ HSᵗ s′ Bs′ ⟧)
      (λ y → hs-par (sumᵇ (gTerms Bs′)) s′ (lay₁ (m ℕ+ m) (str y))
                    (lay₂ (m ℕ+ m) (str y)) (lay₃ (m ℕ+ m) (str y)))
      (λ w y → lay₃ (m ℕ+ m) (str y) w)
  tool-tracks = record { phase-at = ph ; out-at = ob }
    where
    n : ℕ
    n = m ℕ+ m

    ξ′ : PathSum n (norm (HSᵗ s′ Bs′)) (paths (HSᵗ s′ Bs′))
    ξ′ = at0 ⟦ HSᵗ s′ Bs′ ⟧

    ph : ∀ x y →
         pow M ∣ (eval (phase ξ′) x y -
                  ½ * [ hs-par (sumᵇ (gTerms Bs′)) s′ (lay₁ n (str y))
                               (lay₂ n (str y)) (lay₃ n (str y)) ]ᶻ)
    ph x y = subst (pow M ∣_)
      (cong₂ _-_ (sym evalEq) (+-identityˡ _))
      (runsˣ-φ (runs-HSᵗ s′ Bs′ (str y)) 0ℤ)
      where
      evalEq : eval (phase ξ′) x y ≡
               proj₁ (traceˣ (HSᵗ s′ Bs′) (str y) (0ℤ , 0ᵃ {n}))
      evalEq = trans (eval-at0 (phase ⟦ HSᵗ s′ Bs′ ⟧) x y)
                     (eval-⟦⟧ˣ (HSᵗ s′ Bs′) (0ᵃ {n}) y)

    ob : ∀ w x y → odd (eval (out ξ′ w) x y) ≡ lay₃ n (str y) w
    ob w x y = trans (cong odd (eval-at0 (out ⟦ HSᵗ s′ Bs′ ⟧ w) x y))
      (trans (outBit-⟦⟧ˣ (HSᵗ s′ Bs′) (0ᵃ {n}) y w)
             (runsˣ-v (runs-HSᵗ s′ Bs′ (str y)) 0ℤ w))

private
  tracksᵗ : Tracks (at0 ⟦ HSᵗ s Bs ⟧) (evalᴿ pFᵗ) (λ w → evalᴿ (pGᵗ w))
  tracksᵗ = tracks-cong (tool-tracks s Bs) parity-ANFᵗ out-ANFᵗ

open Reduce (at0 ⟦ HSᵗ s Bs ⟧)

private
  st₀ : Stage 24 pFᵗ pGᵗ
  st₀ = stage (at0 ⟦ HSᵗ s Bs ⟧) εᶠ tracksᵗ

  -- The six steps, each stage named (see PathSum.HiddenShift.Stuck).

  st₁ : Stage 22 _ _
  st₁ = step st₀ (# 23) (# 15) refl refl   -- [HH] at a₀, c₀ ← a₁ ⊕ a₂ ⊕ b₀

  st₂ : Stage 20 _ _
  st₂ = step st₁ (# 18) (# 7) refl refl    -- [HH] at b₀, e₀ ← 0

  st₃ : Stage 18 _ _
  st₃ = step st₂ (# 14) (# 7) refl refl    -- [HH] at b₃, d₃ ← a₃

  st₄ : Stage 16 _ _
  st₄ = step st₃ (# 10) (# 4) refl refl    -- [HH] at c₃, e₃ ← 0

  st₅ : Stage 14 _ _
  st₅ = step st₄ (# 8) (# 7) refl refl     -- [HH] at d₀, d₁ ← a₁ ⊕ a₂ ⊕ d₂ ⊕ h₀

  st₆ : Stage 12 _ _
  st₆ = step st₅ (# 12) (# 2) refl refl    -- [HH] at a₂, h₁ ← a₁a₃ ⊕ b₁ ⊕ …

  finish : ∀ {pF pG} → Stage 12 pF pG → eqᴿ pF endFᵗ ≡ true →
           allFin (λ w → eqᴿ (pG w) (endGᵗ w)) ≡ true →
           Σ (PathSum 8 12 12) (λ ζ → (at0 ⟦ HSᵗ s Bs ⟧ ⟶ᶠ* ζ) × Irreducibleᶠ ζ)
  finish {pF} {pG} st eF eG =
    ξ st , chain st , occurs⇒irreducible (ξ st) {endFᵗ} {endGᵗ} tr end-occursᵗ
    where
    tr : Tracks (ξ st) (evalᴿ endFᵗ) (λ w → evalᴿ (endGᵗ w))
    tr = tracks-cong (tracks st)
      (λ y → cong (λ p → evalᴿ p y) (eqᴿ-sound pF endFᵗ eF))
      (λ w y → cong (λ p → evalᴿ p y)
        (eqᴿ-sound (pG w) (endGᵗ w)
          (allFin-sound (λ w′ → eqᴿ (pG w′) (endGᵗ w′)) eG w)))

-- The tool's hidden shift circuit for this draw, on |0⟩: six [HH]
-- steps, each followed by an [Elim], reach a path-sum with twelve
-- path variables to which no rule of figure 2 applies; the last [HH]'s
-- quotient is not linear.

tool-stuck :
  Σ (PathSum 8 12 12) (λ ζ → (at0 ⟦ HSᵗ s Bs ⟧ ⟶ᶠ* ζ) × Irreducibleᶠ ζ)
tool-stuck = finish st₆ refl refl
