------------------------------------------------------------------------
-- Presentations of groups
--
-- The layers of the hidden shift circuits over {H, X, CNOT, R_k, R_k†},
-- X a primitive gate (Amy, QPL 2018, section 5.2)
--
-- The paper's tool, Feynman, writes the shift of its hidden shift
-- benchmarks as X gates, and counts X as a primitive Clifford gate
-- with no path variable: table 2's hidden shift rows have 3n path
-- variables.  PathSum.HiddenShift.Layers builds X as H R₁ H over
-- {H, CNOT, R_k, R_k†}, two more Hadamards per X gate.  This module
-- redoes the layers over PathSum.CRK.WithX, where X is a gate of its
-- own, |x⟩ ↦ |1 ⊕ x⟩:
--
--  * A circuit over {H, CNOT, R_k, R_k†}, embedded (map embed), acts
--    on columns as it did (applyᴬ-embed), so it simulates the same
--    path-sums (Sim-embed, in the sense of PathSum.HiddenShift.Layers's
--    Sim) and has the same amplitudes (amp-embed).  Everything proved
--    there about the Hadamard layer and the oracles carries over.
--  * The X layer X^s has an X on every wire where s is 1, in
--    increasing order of the wires, as the tool's map X s writes it
--    (flipsˣ).  It shifts a column by s with no normalisation
--    (applyᴬ-flipsˣ) -- where Layers's H R₁ H version picks up the
--    factor 2 = √2² of its Hadamards -- and an oracle conjugated by it
--    simulates the oracle of the shifted exponent with scale 0
--    (Sim-shiftedˣ).
--  * Simulations compose along concatenation, and a circuit that
--    simulates a path-sum has its amplitudes (proposition 2.10, now
--    PathSum.CRK.WithX's), so is equivalent to it when the
--    normalisations match (Sim-++ˣ, Sim-circuitˣ, Sim-≋ˣ).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.LayersX (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (_*_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import PathSum.AmpLinear M₀ using (scale-+; scale-exp)
open import PathSum.Assign using (_[_≔_])
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.Base using (PathSum)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using (applyᴾ)
open import PathSum.Cyclotomic M₀ using (_≐_; scale; scale-map; Respects)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.HiddenShift M₀ using (Oᴾ; shiftᴾ; boolᴾ; bool-shiftᴾ)
open import PathSum.HiddenShift.Gates M₀ using
  (∷ᵃ-≔; ∷ᵃ-η; slice-resp; Signs; signed)
open import PathSum.HiddenShift.Layers M₀ using
  (Sim; sim; Sim-∘; Sim-ext; Sim-δ; applyᴾ-Oᴾ′)
open import PathSum.HiddenShift.Walsh using (_⊕ᵃ_)
open import PathSum.Polynomial using (Poly; sgn)

private
  M : ℕ
  M = suc (suc (suc M₀))

import PathSum.CRK.Circuit
import PathSum.CRK.Semantics

private
  module CRK  = PathSum.CRK.Circuit M
  module CRKˢ = PathSum.CRK.Semantics M₀

open import PathSum.CRK.WithX M₀ using
  (Gate; H; X; CNOT; R; R†; Circuit; norm; ⟦_⟧; embed; gateᴬ; applyᴬ;
   applyᴬ-++; applyᴬ-cong; applyᴬ-resp; gateᴬ-resp; prop-2-10)

private
  variable
    n k k′ m m′ : ℕ


------------------------------------------------------------------------
-- Circuits without X

-- An embedded gate, and so an embedded circuit, acts on columns as it
-- did over {H, CNOT, R_k, R_k†}.

gateᴬ-embed : (g : CRK.Gate n) (ψ : Column n) →
              ∀ z → gateᴬ (embed g) ψ z ≐ CRKˢ.gateᴬ g ψ z
gateᴬ-embed (CRK.H w)        ψ z i = refl
gateᴬ-embed (CRK.CNOT c t p) ψ z i = refl
gateᴬ-embed (CRK.R k w)      ψ z i = refl
gateᴬ-embed (CRK.R† k w)     ψ z i = refl

applyᴬ-embed : (C : CRK.Circuit n) (ψ : Column n) →
               ∀ z → applyᴬ (map embed C) ψ z ≐ CRKˢ.applyᴬ C ψ z
applyᴬ-embed []      ψ z i = refl
applyᴬ-embed (g ∷ C) ψ z i =
  trans (applyᴬ-embed C (gateᴬ (embed g) ψ) z i)
        (CRKˢ.applyᴬ-cong C (gateᴬ-embed g ψ) z i)

-- So it has the same amplitudes.

amp-embed : (C : CRK.Circuit n) (x z : Assign n) →
            amp ⟦ map embed C ⟧ x z ≐ amp (CRK.⟦ C ⟧) x z
amp-embed C x z i = trans (prop-2-10 (map embed C) x z i)
  (trans (applyᴬ-embed C (δ x) z i) (sym (CRKˢ.prop-2-10 C x z i)))

-- Normalisations add up along a concatenation.

norm-++ˣ : (C D : Circuit n) → norm (C ++ D) ≡ norm C ℕ+ norm D
norm-++ˣ []               D = refl
norm-++ˣ (H _ ∷ C)        D = cong suc (norm-++ˣ C D)
norm-++ˣ (X _ ∷ C)        D = norm-++ˣ C D
norm-++ˣ (CNOT _ _ _ ∷ C) D = norm-++ˣ C D
norm-++ˣ (R _ _ ∷ C)      D = norm-++ˣ C D
norm-++ˣ (R† _ _ ∷ C)     D = norm-++ˣ C D


------------------------------------------------------------------------
-- Simulation

-- An embedded circuit simulates what it simulated.

Sim-embed : (C : CRK.Circuit n) {ξ : PathSum n k m} {e : ℕ} →
            Sim (CRKˢ.applyᴬ C) ξ e → Sim (applyᴬ (map embed C)) ξ e
Sim-embed C S = Sim-ext S (λ ψ r z → applyᴬ-embed C ψ z)

-- Concatenation is composition, and a circuit simulating ξ has ξ's
-- amplitudes (proposition 2.10 with X).

Sim-++ˣ : (C D : Circuit n) {ξ : PathSum n k m} {ξ′ : PathSum n k′ m′}
          {e e′ : ℕ} →
          Sim (applyᴬ C) ξ e → Sim (applyᴬ D) ξ′ e′ →
          Sim (applyᴬ (C ++ D)) (ξ′ ∘ᴾ ξ) (e′ ℕ+ e)
Sim-++ˣ C D S S′ =
  Sim-ext (Sim-∘ S S′) (λ ψ r z i → cong (λ F → F z i) (applyᴬ-++ C D ψ))

Sim-circuitˣ : (C : Circuit n) {ξ : PathSum n k m} {e : ℕ} →
               Sim (applyᴬ C) ξ e →
               ∀ x z → amp ⟦ C ⟧ x z ≐ scale e (amp ξ x z)
Sim-circuitˣ C S x z i = trans (prop-2-10 C x z i) (Sim-δ S x z i)

Sim-≋ˣ : (C : Circuit n) (ξ : PathSum n k m) {e : ℕ} →
         Sim (applyᴬ C) ξ e → norm C ≡ k ℕ+ e → ⟦ C ⟧ ≋ ξ
Sim-≋ˣ {k = k} C ξ {e} S eq x z i = trans
  (scale-map k (Sim-circuitˣ C S x z) i)
  (trans (scale-+ k e (amp ξ x z) i)
         (scale-exp (amp ξ x z) (sym eq) i))


------------------------------------------------------------------------
-- The X layer

-- The wires where s is 1, in increasing order.

selʰ : Bool → List (Fin (suc n)) → List (Fin (suc n))
selʰ false ws = ws
selʰ true  ws = zero ∷ ws

sel : Assign n → List (Fin n)
sel {zero}  s = []
sel {suc n} s = selʰ (s zero) (map suc (sel (λ i → s (suc i))))

-- X^s: an X on each of them.

flipsˣ : Assign n → Circuit n
flipsˣ s = map X (sel s)

norm-Xs : (ws : List (Fin n)) → norm (map X ws) ≡ 0
norm-Xs []       = refl
norm-Xs (w ∷ ws) = norm-Xs ws

norm-flipsˣ : (s : Assign n) → norm (flipsˣ s) ≡ 0
norm-flipsˣ s = norm-Xs (sel s)

-- X gates on the wires 1 … n of n + 1 act on every slice with the
-- first bit fixed.

Xs-lift : (ws : List (Fin n)) {ψ : Column (suc n)} → Respects ψ →
          ∀ b u → applyᴬ (map X (map suc ws)) ψ (b ∷ᵃ u) ≐
                  applyᴬ (map X ws) (λ u′ → ψ (b ∷ᵃ u′)) u
Xs-lift []       r b u i = refl
Xs-lift (w ∷ ws) {ψ} r b u i =
  trans (Xs-lift ws (gateᴬ-resp (X (suc w)) r) b u i)
        (applyᴬ-cong (map X ws) {λ u′ → gateᴬ (X (suc w)) ψ (b ∷ᵃ u′)}
                     {gateᴬ (X w) (λ u′ → ψ (b ∷ᵃ u′))}
                     (λ u′ → r _ _ (∷ᵃ-≔ b u′ w (not (u′ w)))) u i)

private
  xor-true : ∀ a → not a ≡ a xor true
  xor-true false = refl
  xor-true true  = refl

  xor-back : ∀ a b → (a xor b) xor b ≡ a
  xor-back false false = refl
  xor-back false true  = refl
  xor-back true  false = refl
  xor-back true  true  = refl

-- X^s shifts a column by s, with no normalisation.

applyᴬ-flipsˣ : (s : Assign n) (ψ : Column n) → Respects ψ →
                ∀ z → applyᴬ (flipsˣ s) ψ z ≐ ψ (z ⊕ᵃ s)
applyᴬ-flipsˣ {zero}  s ψ r z = r z (z ⊕ᵃ s) (λ ())
applyᴬ-flipsˣ {suc n} s ψ r z = step (s zero) refl
  where
  ts tz : Assign n
  ts j = s (suc j)
  tz j = z (suc j)

  -- The X gates on the wires 1 … n shift the slice of z.

  rest : (φ : Column (suc n)) → Respects φ →
         applyᴬ (map X (map suc (sel ts))) φ z ≐ φ (z zero ∷ᵃ (tz ⊕ᵃ ts))
  rest φ rφ i =
    trans (applyᴬ-resp (map X (map suc (sel ts))) rφ z (z zero ∷ᵃ tz)
                       (∷ᵃ-η z) i)
      (trans (Xs-lift (sel ts) rφ (z zero) tz i)
             (applyᴬ-flipsˣ ts (λ u′ → φ (z zero ∷ᵃ u′))
                            (slice-resp rφ (z zero)) tz i))

  step : ∀ b → s zero ≡ b →
         applyᴬ (map X (selʰ b (map suc (sel ts)))) ψ z ≐ ψ (z ⊕ᵃ s)
  step false e i = trans (rest ψ r i) (r _ _ at i)
    where
    at : ∀ j → (z zero ∷ᵃ (tz ⊕ᵃ ts)) j ≡ (z ⊕ᵃ s) j
    at zero    = trans (sym (xor-identityʳ (z zero)))
                       (cong (z zero xor_) (sym e))
    at (suc j) = refl
  step true  e i =
    trans (rest (gateᴬ (X zero) ψ) (gateᴬ-resp (X zero) r) i) (r _ _ at i)
    where
    at : ∀ j → ((z zero ∷ᵃ (tz ⊕ᵃ ts)) [ zero ≔ not (z zero) ]) j ≡
               (z ⊕ᵃ s) j
    at zero    = trans (xor-true (z zero)) (cong (z zero xor_) (sym e))
    at (suc j) = refl

-- An embedded circuit multiplying by the sign of b, conjugated by X^s,
-- is the oracle of the shifted exponent: Layers's Sim-shifted without
-- the Hadamards of H R₁ H.

private
  shifted-at : (s : Assign n) {C : CRK.Circuit n} {b : Assign n → Bool} →
               Signs C b → (E : Poly n 0) → (∀ z → b z ≡ boolᴾ E z) →
               (ψ : Column n) → Respects ψ → ∀ z →
               applyᴬ (flipsˣ s ++ (map embed C ++ flipsˣ s)) ψ z ≐
               applyᴾ (Oᴾ (shiftᴾ s E)) ψ z
  shifted-at s {C} {b} sC E h ψ r z i =
    trans (cong (λ F → F z i)
                (applyᴬ-++ (flipsˣ s) (map embed C ++ flipsˣ s) ψ))
      (trans (cong (λ F → F z i) (applyᴬ-++ (map embed C) (flipsˣ s) φ))
        (trans (applyᴬ-flipsˣ s (applyᴬ (map embed C) φ)
                              (applyᴬ-resp (map embed C) φr) z i)
          (trans (applyᴬ-embed C φ (z ⊕ᵃ s) i)
            (trans (signed sC φ φr (z ⊕ᵃ s) i)
              (trans (cong (sgn (b (z ⊕ᵃ s)) *_)
                           (trans (applyᴬ-flipsˣ s ψ r (z ⊕ᵃ s) i)
                                  (r _ z (λ j → xor-back (z j) (s j)) i)))
                (trans (cong (λ t → sgn t * ψ z i)
                             (trans (h (z ⊕ᵃ s)) (sym (bool-shiftᴾ s E z))))
                       (sym (applyᴾ-Oᴾ′ (shiftᴾ s E) ψ r z i))))))))
    where
    φ : Column _
    φ = applyᴬ (flipsˣ s) ψ

    φr : Respects φ
    φr = applyᴬ-resp (flipsˣ s) r

Sim-shiftedˣ : (s : Assign n) {C : CRK.Circuit n} {b : Assign n → Bool} →
               Signs C b → (E : Poly n 0) → (∀ z → b z ≡ boolᴾ E z) →
               Sim (applyᴬ (flipsˣ s ++ (map embed C ++ flipsˣ s)))
                   (Oᴾ (shiftᴾ s E)) 0
Sim-shiftedˣ s {C} sC E h =
  sim (λ ψ r → applyᴬ-resp (flipsˣ s ++ (map embed C ++ flipsˣ s)) r)
      (shifted-at s sC E h)
