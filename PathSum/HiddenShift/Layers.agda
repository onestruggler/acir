------------------------------------------------------------------------
-- Presentations of groups
--
-- The layers of the hidden shift circuits on columns, and circuits
-- simulating path-sums (Amy, QPL 2018, section 5.2)
--
-- The circuit H^{⊗n} is a Hadamard on every wire (hadamards n).  On a
-- column ψ it computes the Walsh-Hadamard transform, the entry at z
-- becoming Σ_w (-1)^{w·z} ψ(w) unnormalised (applyᴬ-hadamards): by
-- induction on n, the Hadamard on wire 0 pairing the two halves of the
-- column and the rest acting on each half (PathSum.HiddenShift.Gates's
-- applyᴬ-lift).  The path-sum Hᴾ of PathSum.HiddenShift acts on
-- columns the same way (applyᴾ-Hᴾ′), and an oracle Oᴾ E multiplies the
-- entry at z by (-1)^{E(z)} (applyᴾ-Oᴾ′); PathSum.HiddenShift proved
-- both on columns of integers, and here they are proved on every
-- column.
--
-- X is not a gate of {H, CNOT, R_k, R_k†}: it is H R₁ H here (Xᶜ),
-- which sends the entry at z to 2 ψ(z with bit w flipped) -- the 2 is
-- √2², the two Hadamards' normalisation (applyᴬ-X).  The layer X^s
-- (flips s) has an X on every wire where s is 1, and shifts the column
-- by s (applyᴬ-flips).  An oracle conjugated by X^s is the oracle of
-- the shifted function (Sim-shifted), which is how figure 3(a) builds
-- O_f′ from O_f.
--
-- Simulation.  Sim L ξ e says the operator L on columns is the
-- operator U_ξ of the path-sum ξ (PathSum.Compose.Properties's
-- applyᴾ) scaled by √2^e, on every column that reads assignments
-- through their values.  It composes along definition 2.6: if L
-- simulates ξ and L′ simulates ξ′, then L′ ∘ L simulates ξ′ ∘ᴾ ξ
-- (Sim-∘, by the functoriality applyᴾ-∘ of proposition 2.7), and for
-- circuits C ++ D simulates ⟦D⟧ ∘ ⟦C⟧'s counterpart (Sim-++).  A
-- circuit that simulates ξ has ξ's amplitudes, by proposition 2.10
-- (Sim-circuit), and so is equivalent to it in the sense of definition
-- 2.3 when the normalisations match (Sim-≋).  So H^{⊗n} is equivalent
-- to Hᴾ (hadamards-≋), and the circuit of a list of monomials to the
-- oracle of any polynomial with the same parities (oracle-≋).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Layers (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using (*-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.AmpLinear M₀ using (scale-+; scale-exp; scale-comm)
open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-≔; same)
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.Base using (PathSum; phase)
open import PathSum.CircuitSemantics M₀ using (Column; δ; δ-resp)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using
  (applyᴾ; applyᴾ-cong; applyᴾ-scale; applyᴾ-∘; amp-applyᴾ)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; _·ᴬ_; _+ᴬ_; extend; Σᴮ; Σᴮ-cong; Σᴮ-+; rot; rot-map;
   rot-exp; scale; scale-map; scale-·ᴬ; √2·-twice; Respects)
open import PathSum.Denotation M₀ using (Assign; amp; hits; _≋_)
open import PathSum.HiddenShift M₀ using
  (Hᴾ; Oᴾ; hdotᴾ; odd-dotᴾ; hits-Hᴾ; hits-Oᴾ; boolᴾ; boolᴾ-resp; none;
   eval-none; Σᴮ-none; shiftᴾ; bool-shiftᴾ; same-comm)
open import PathSum.HiddenShift.Gates M₀ using
  (rot-½-bit; rot-½ᴬ; lift; norm-lift; applyᴬ-lift; ∷ᵃ-η; slice-resp;
   Signs; signed; Term; oracle; sumᵇ; Signs-oracle; norm-oracle)
open import PathSum.HiddenShift.Walsh using (dot; _⊕ᵃ_; sgn-xor)
open import PathSum.Polynomial using (Poly; x[_]; y[_]; eval; sgn)
open import PathSum.Polynomial.Properties using (eval-·ᴾ; eval-cong)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; :-_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using (Gate; H; R; Circuit; norm; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; applyᴬ-++; applyᴬ-resp; gateᴬ-resp; prop-2-10)
open import PathSum.Reduction M using (½)

private
  variable
    n k k′ m m′ : ℕ


------------------------------------------------------------------------
-- The path-sums on every column

-- The Walsh-Hadamard transform of a column, unnormalised.

WH : Column n → Column n
WH ψ z = Σᴮ (λ w → sgn (dot w z) ·ᴬ ψ w)

-- The Hadamard layer of PathSum.HiddenShift computes it.

applyᴾ-Hᴾ′ : (ψ : Column n) (z : Assign n) → applyᴾ (Hᴾ {n}) ψ z ≐ WH ψ z
applyᴾ-Hᴾ′ {n} ψ z i =
  Σᴮ-cong {f = λ w → Σᴮ (λ y → if hits (Hᴾ {n}) w y z then G w y else 0ᴬ)}
          {g = λ w → sgn (dot w z) ·ᴬ ψ w} inner i
  where
  G : Assign n → Assign n → Amp
  G w y = rot (eval (phase (Hᴾ {n})) w y) (ψ w)

  G-resp : ∀ w → Respects (G w)
  G-resp w g h g≗h = rot-exp {eval (phase (Hᴾ {n})) w g}
    {eval (phase (Hᴾ {n})) w h} (ψ w)
    (eval-cong (phase (Hᴾ {n})) {w} {w} {g} {h} (λ _ → refl) g≗h)

  inner : ∀ w → Σᴮ (λ y → if hits (Hᴾ {n}) w y z then G w y else 0ᴬ) ≐
                sgn (dot w z) ·ᴬ ψ w
  inner w l = trans
    (Σᴮ-cong {f = λ y → if hits (Hᴾ {n}) w y z then G w y else 0ᴬ}
             {g = λ y → if same z y then G w y else 0ᴬ}
             (λ y → if-cong (hits-Hᴾ w y z) (λ _ → refl)) l)
    (trans (Σᴮ-δ z (G w) (G-resp w) l)
      (trans (rot-exp {eval (phase (Hᴾ {n})) w z} {½ * eval hdotᴾ w z}
                      (ψ w) (eval-·ᴾ ½ hdotᴾ w z) l)
        (trans (rot-½ᴬ (eval hdotᴾ w z) (ψ w) l)
               (cong (λ b → sgn b * ψ w l)
                     (odd-dotᴾ (λ v → x[ v ]) (λ v → y[ v ]) w z)))))

-- An oracle multiplies the entry at z by the sign of its exponent.

applyᴾ-Oᴾ′ : (E : Poly n 0) (ψ : Column n) → Respects ψ →
             ∀ z → applyᴾ (Oᴾ E) ψ z ≐ sgn (boolᴾ E z) ·ᴬ ψ z
applyᴾ-Oᴾ′ {n} E ψ resp z i = trans
  (Σᴮ-cong {f = λ w → Σᴮ (λ y → T w y)}
           {g = λ w → if same z w then F w else 0ᴬ}
           (λ w → Σᴮ-none (T w) (per w)) i)
  (Σᴮ-δ z F F-resp i)
  where
  T : Assign n → Assign 0 → Amp
  T w y = if hits (Oᴾ E) w y z
          then rot (eval (phase (Oᴾ E)) w y) (ψ w) else 0ᴬ

  F : Assign n → Amp
  F w = sgn (boolᴾ E w) ·ᴬ ψ w

  per : ∀ w y → T w y ≐ (if same z w then F w else 0ᴬ)
  per w y = if-cong (trans (hits-Oᴾ E w y z) (same-comm w z)) (λ l → trans
    (rot-exp {eval (phase (Oᴾ E)) w y} {½ * eval E w none} (ψ w)
             (trans (eval-·ᴾ ½ E w y) (cong (½ *_) (eval-none E w y))) l)
    (rot-½ᴬ (eval E w none) (ψ w) l))

  F-resp : Respects F
  F-resp g h g≗h l =
    cong₂ (λ a b → sgn a * b) (boolᴾ-resp E g h g≗h) (resp g h g≗h l)


------------------------------------------------------------------------
-- The Hadamard layer

-- A Hadamard on every wire, wire 0 first.

hadamards : ∀ n → Circuit n
hadamards zero    = []
hadamards (suc n) = H zero ∷ lift (hadamards n)

norm-hadamards : ∀ n → norm (hadamards n) ≡ n
norm-hadamards zero    = refl
norm-hadamards (suc n) =
  cong suc (trans (norm-lift (hadamards n)) (norm-hadamards n))

-- Setting the head bit.

private
  head-≔ : (b c : Bool) (u : Assign n) →
           ∀ j → ((b ∷ᵃ u) [ zero ≔ c ]) j ≡ (c ∷ᵃ u) j
  head-≔ b c u zero    = refl
  head-≔ b c u (suc j) = refl

  ∷ᵃ-extend : (b : Bool) (u : Assign n) → ∀ j → (b ∷ᵃ u) j ≡ extend b u j
  ∷ᵃ-extend b u zero    = refl
  ∷ᵃ-extend b u (suc j) = refl

-- It computes the Walsh-Hadamard transform.  The Hadamard on wire 0
-- turns the slice at z₀ into ψ(0 u) + (-1)^{z₀} ψ(1 u), the rest
-- transforms that slice, and the two halves of the sum over w are the
-- terms with w₀ = 1 and w₀ = 0.

applyᴬ-hadamards : ∀ n (ψ : Column n) → Respects ψ →
                   ∀ z → applyᴬ (hadamards n) ψ z ≐ WH ψ z
applyᴬ-hadamards zero    ψ resp z i =
  trans (resp z (λ ()) (λ ()) i) (sym (*-identityˡ (ψ (λ ()) i)))
applyᴬ-hadamards (suc n) ψ resp z i =
  trans (applyᴬ-resp (lift (hadamards n)) φ-resp z (z zero ∷ᵃ tz) (∷ᵃ-η z) i)
    (trans (applyᴬ-lift (hadamards n) φ-resp (z zero) tz i)
      (trans (applyᴬ-hadamards n σ (slice-resp φ-resp (z zero)) tz i)
             combine))
  where
  tz : Assign n
  tz j = z (suc j)

  φ : Column (suc n)
  φ = gateᴬ (H zero) ψ

  φ-resp : Respects φ
  φ-resp = gateᴬ-resp (H zero) resp

  σ : Column n
  σ u = φ (z zero ∷ᵃ u)

  σ-value : ∀ u → σ u ≐ ψ (false ∷ᵃ u) +ᴬ sgn (z zero) ·ᴬ ψ (true ∷ᵃ u)
  σ-value u l = cong₂ _+_ (resp _ _ (head-≔ (z zero) false u) l)
    (trans (rot-map (½ * [ z zero ]ᶻ) (resp _ _ (head-≔ (z zero) true u)) l)
           (rot-½-bit (z zero) (ψ (true ∷ᵃ u)) l))

  Tr Fa : Assign n → Amp
  Tr u = sgn (z zero xor dot u tz) ·ᴬ ψ (true ∷ᵃ u)
  Fa u = sgn (dot u tz) ·ᴬ ψ (false ∷ᵃ u)

  alg : ∀ s t A B → s * (A + t * B) ≡ (t * s) * B + s * A
  alg = solve 4 (λ s t A B → s :* (A :+ t :* B) := (t :* s) :* B :+ s :* A)
                refl

  per-u : ∀ u → sgn (dot u tz) ·ᴬ σ u ≐ Tr u +ᴬ Fa u
  per-u u l = trans (cong (sgn (dot u tz) *_) (σ-value u l))
    (trans (alg (sgn (dot u tz)) (sgn (z zero)) (ψ (false ∷ᵃ u) l)
                (ψ (true ∷ᵃ u) l))
           (cong (λ t → t * ψ (true ∷ᵃ u) l + sgn (dot u tz) * ψ (false ∷ᵃ u) l)
                 (sym (sgn-xor (z zero) (dot u tz)))))

  combine : WH σ tz i ≡ WH ψ z i
  combine = trans (Σᴮ-cong {f = λ u → sgn (dot u tz) ·ᴬ σ u}
                           {g = λ u → Tr u +ᴬ Fa u} per-u i)
    (trans (Σᴮ-+ Tr Fa i)
      (cong₂ _+_
        (Σᴮ-cong {f = Tr}
                 {g = λ g → sgn (dot (extend true g) z) ·ᴬ ψ (extend true g)}
                 (λ g l → cong (sgn (z zero xor dot g tz) *_)
                               (resp _ _ (∷ᵃ-extend true g) l)) i)
        (Σᴮ-cong {f = Fa}
                 {g = λ g → sgn (dot (extend false g) z) ·ᴬ ψ (extend false g)}
                 (λ g l → cong (sgn (dot g tz) *_)
                               (resp _ _ (∷ᵃ-extend false g) l)) i)))


------------------------------------------------------------------------
-- The X layer

-- X = H R₁ H.

Xᶜ : Fin n → Circuit n
Xᶜ w = H w ∷ R 1 w ∷ H w ∷ []

-- It flips its wire, with the factor 2 = √2² of its two Hadamards.

applyᴬ-X : (w : Fin n) (ψ : Column n) → Respects ψ →
           ∀ z → applyᴬ (Xᶜ w) ψ z ≐ scale 2 (ψ (z [ w ≔ not (z w) ]))
applyᴬ-X w ψ resp z i = trans
  (cong₂ _+_ (mid false i)
    (trans (rot-map (½ * [ z w ]ᶻ) (mid true) i)
           (rot-½-bit (z w) (sgn true ·ᴬ (A +ᴬ sgn true ·ᴬ B)) i)))
  (trans (fin (z w)) (sym (√2·-twice (ψ (z [ w ≔ not (z w) ])) i)))
  where
  A B : Amp
  A = ψ (z [ w ≔ false ])
  B = ψ (z [ w ≔ true ])

  φ₁ φ₂ : Column _
  φ₁ = gateᴬ (H w) ψ
  φ₂ = gateᴬ (R 1 w) φ₁

  inner : ∀ c → φ₁ (z [ w ≔ c ]) ≐ A +ᴬ sgn c ·ᴬ B
  inner c l = cong₂ _+_ (resp _ _ (≔-≔ z w c false) l)
    (trans (rot-exp {½ * [ (z [ w ≔ c ]) w ]ᶻ} {½ * [ c ]ᶻ}
                    (ψ ((z [ w ≔ c ]) [ w ≔ true ]))
                    (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w c)) l)
      (trans (rot-map (½ * [ c ]ᶻ) (resp _ _ (≔-≔ z w c true)) l)
             (rot-½-bit c B l)))

  mid : ∀ c → φ₂ (z [ w ≔ c ]) ≐ sgn c ·ᴬ (A +ᴬ sgn c ·ᴬ B)
  mid c l = trans
    (rot-exp {½ * [ (z [ w ≔ c ]) w ]ᶻ} {½ * [ c ]ᶻ} (φ₁ (z [ w ≔ c ]))
             (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w c)) l)
    (trans (rot-map (½ * [ c ]ᶻ) (inner c) l)
           (rot-½-bit c (A +ᴬ sgn c ·ᴬ B) l))

  fin : ∀ b → (1ℤ * (A i + 1ℤ * B i)) + sgn b * (- 1ℤ * (A i + - 1ℤ * B i)) ≡
              (+ 2) * ψ (z [ w ≔ not b ]) i
  fin false = solve 2 (λ a b → (con 1ℤ :* (a :+ con 1ℤ :* b)) :+
                                con 1ℤ :* (con (- 1ℤ) :* (a :+ con (- 1ℤ) :* b))
                               := con (+ 2) :* b) refl (A i) (B i)
  fin true  = solve 2 (λ a b → (con 1ℤ :* (a :+ con 1ℤ :* b)) :+
                                con (- 1ℤ) :*
                                  (con (- 1ℤ) :* (a :+ con (- 1ℤ) :* b))
                               := con (+ 2) :* a) refl (A i) (B i)

-- X^s: an X on wire 0 if s₀ = 1, then X^{s′} on the rest.

flipʰ : Bool → Circuit (suc n) → Circuit (suc n)
flipʰ false C = C
flipʰ true  C = Xᶜ zero ++ C

flips : Assign n → Circuit n
flips {zero}  s = []
flips {suc n} s = flipʰ (s zero) (lift (flips (λ i → s (suc i))))

-- It shifts a column by s.

private
  xor-true : ∀ a → not a ≡ a xor true
  xor-true false = refl
  xor-true true  = refl

  flip-step : (b : Bool) (t : Assign n) (C : Circuit n) →
              (∀ φ → Respects φ → ∀ u →
                 applyᴬ C φ u ≐ scale (norm C) (φ (u ⊕ᵃ t))) →
              (ψ : Column (suc n)) → Respects ψ → ∀ z →
              applyᴬ (flipʰ b (lift C)) ψ z ≐
              scale (norm (flipʰ b (lift C))) (ψ (z ⊕ᵃ (b ∷ᵃ t)))
  flip-step {n} false t C hC ψ resp z i =
    trans (applyᴬ-resp (lift C) resp z (z zero ∷ᵃ tz) (∷ᵃ-η z) i)
      (trans (applyᴬ-lift C resp (z zero) tz i)
        (trans (hC (λ u → ψ (z zero ∷ᵃ u)) (slice-resp resp (z zero)) tz i)
          (trans (scale-map (norm C) (resp _ _ at) i)
                 (scale-exp (ψ (z ⊕ᵃ (false ∷ᵃ t)))
                            (sym (norm-lift C)) i))))
    where
    tz : Assign n
    tz j = z (suc j)

    at : ∀ j → (z zero ∷ᵃ (tz ⊕ᵃ t)) j ≡ (z ⊕ᵃ (false ∷ᵃ t)) j
    at zero    = sym (xor-identityʳ (z zero))
    at (suc j) = refl
  flip-step {n} true t C hC ψ resp z i =
    trans (applyᴬ-resp (lift C) χ-resp z (z zero ∷ᵃ tz) (∷ᵃ-η z) i)
      (trans (applyᴬ-lift C χ-resp (z zero) tz i)
        (trans (hC (λ u → χ (z zero ∷ᵃ u)) (slice-resp χ-resp (z zero)) tz i)
          (trans (scale-map (norm C)
                   (applyᴬ-X zero ψ resp (z zero ∷ᵃ (tz ⊕ᵃ t))) i)
            (trans (scale-comm (norm C) 2 _ i)
              (scale-map 2 (λ l → trans
                (scale-map (norm C) (resp _ _ at) l)
                (scale-exp (ψ (z ⊕ᵃ (true ∷ᵃ t))) (sym (norm-lift C)) l)) i)))))
    where
    tz : Assign n
    tz j = z (suc j)

    χ : Column (suc n)
    χ = applyᴬ (Xᶜ zero) ψ

    χ-resp : Respects χ
    χ-resp = applyᴬ-resp (Xᶜ zero) resp

    at : ∀ j → ((z zero ∷ᵃ (tz ⊕ᵃ t)) [ zero ≔ not (z zero) ]) j ≡
               (z ⊕ᵃ (true ∷ᵃ t)) j
    at zero    = xor-true (z zero)
    at (suc j) = refl

applyᴬ-flips : (s : Assign n) (ψ : Column n) → Respects ψ →
               ∀ z → applyᴬ (flips s) ψ z ≐ scale (norm (flips s)) (ψ (z ⊕ᵃ s))
applyᴬ-flips {zero}  s ψ resp z i = resp z (z ⊕ᵃ s) (λ ()) i
applyᴬ-flips {suc n} s ψ resp z i = trans
  (flip-step (s zero) (λ j → s (suc j)) (flips (λ j → s (suc j)))
             (applyᴬ-flips (λ j → s (suc j))) ψ resp z i)
  (scale-map (norm (flips s)) (resp _ _ at) i)
  where
  at : ∀ j → (z ⊕ᵃ (s zero ∷ᵃ (λ j → s (suc j)))) j ≡ (z ⊕ᵃ s) j
  at zero    = refl
  at (suc j) = refl


------------------------------------------------------------------------
-- Simulation

-- The operator L on columns is U_ξ scaled by √2^e, on every column
-- that reads assignments only through their values.

record Sim (L : Column n → Column n) (ξ : PathSum n k m) (e : ℕ) : Set where
  constructor sim
  field
    sim-resp  : (ψ : Column n) → Respects ψ → Respects (L ψ)
    simulates : (ψ : Column n) → Respects ψ →
                ∀ z → L ψ z ≐ scale e (applyᴾ ξ ψ z)

open Sim public

-- Simulations compose along definition 2.6.

Sim-∘ : {L L′ : Column n → Column n} {ξ : PathSum n k m}
        {ξ′ : PathSum n k′ m′} {e e′ : ℕ} →
        Sim L ξ e → Sim L′ ξ′ e′ → Sim (λ ψ → L′ (L ψ)) (ξ′ ∘ᴾ ξ) (e′ ℕ+ e)
Sim-∘ {L = L} {L′} {ξ} {ξ′} {e} {e′} S S′ = sim
  (λ ψ r → sim-resp S′ (L ψ) (sim-resp S ψ r))
  (λ ψ r z i → trans (simulates S′ (L ψ) (sim-resp S ψ r) z i)
    (trans (scale-map e′ (applyᴾ-cong ξ′ {L ψ}
                            {λ w → scale e (applyᴾ ξ ψ w)}
                            (simulates S ψ r) z) i)
      (trans (scale-map e′ (λ j → sym (applyᴾ-scale ξ′ e (applyᴾ ξ ψ) z j)) i)
        (trans (scale-+ e′ e (applyᴾ ξ′ (applyᴾ ξ ψ) z) i)
               (scale-map (e′ ℕ+ e) (λ j → sym (applyᴾ-∘ ξ′ ξ ψ z j)) i)))))

-- An operator equal to a simulating one simulates, and the scale may
-- be rewritten.

Sim-ext : {L L′ : Column n → Column n} {ξ : PathSum n k m} {e : ℕ} →
          Sim L ξ e → (∀ ψ → Respects ψ → ∀ z → L′ ψ z ≐ L ψ z) →
          Sim L′ ξ e
Sim-ext {L = L} {L′} S h = sim
  (λ ψ r g g′ g≗g′ i → trans (h ψ r g i)
    (trans (sim-resp S ψ r g g′ g≗g′ i) (sym (h ψ r g′ i))))
  (λ ψ r z i → trans (h ψ r z i) (simulates S ψ r z i))

Sim-exp : {L : Column n → Column n} {ξ : PathSum n k m} {e e′ : ℕ} →
          Sim L ξ e → e ≡ e′ → Sim L ξ e′
Sim-exp {ξ = ξ} S refl = S

-- On a basis column: the amplitudes of ξ.

Sim-δ : {L : Column n → Column n} {ξ : PathSum n k m} {e : ℕ} →
        Sim L ξ e → ∀ x z → L (δ x) z ≐ scale e (amp ξ x z)
Sim-δ {ξ = ξ} {e} S x z i = trans (simulates S (δ x) (δ-resp x) z i)
  (scale-map e (λ j → sym (amp-applyᴾ ξ x z j)) i)

-- Circuits: concatenation is composition, and a circuit simulating ξ
-- has ξ's amplitudes (proposition 2.10).

Sim-++ : (C D : Circuit n) {ξ : PathSum n k m} {ξ′ : PathSum n k′ m′}
         {e e′ : ℕ} →
         Sim (applyᴬ C) ξ e → Sim (applyᴬ D) ξ′ e′ →
         Sim (applyᴬ (C ++ D)) (ξ′ ∘ᴾ ξ) (e′ ℕ+ e)
Sim-++ C D S S′ =
  Sim-ext (Sim-∘ S S′) (λ ψ r z i → cong (λ F → F z i) (applyᴬ-++ C D ψ))

Sim-circuit : (C : Circuit n) {ξ : PathSum n k m} {e : ℕ} →
              Sim (applyᴬ C) ξ e →
              ∀ x z → amp ⟦ C ⟧ x z ≐ scale e (amp ξ x z)
Sim-circuit C S x z i = trans (prop-2-10 C x z i) (Sim-δ S x z i)

Sim-≋ : (C : Circuit n) (ξ : PathSum n k m) {e : ℕ} →
        Sim (applyᴬ C) ξ e → norm C ≡ k ℕ+ e → ⟦ C ⟧ ≋ ξ
Sim-≋ {k = k} C ξ {e} S eq x z i = trans
  (scale-map k (Sim-circuit C S x z) i)
  (trans (scale-+ k e (amp ξ x z) i)
         (scale-exp (amp ξ x z) (sym eq) i))


------------------------------------------------------------------------
-- The layers simulate the path-sums

-- H^{⊗n} is Hᴾ.

Sim-hadamards : ∀ n → Sim (applyᴬ (hadamards n)) (Hᴾ {n}) 0
Sim-hadamards n = sim (λ ψ r → applyᴬ-resp (hadamards n) r)
  (λ ψ r z i → trans (applyᴬ-hadamards n ψ r z i) (sym (applyᴾ-Hᴾ′ ψ z i)))

hadamards-≋ : ∀ n → ⟦ hadamards n ⟧ ≋ Hᴾ {n}
hadamards-≋ n = Sim-≋ (hadamards n) Hᴾ (Sim-hadamards n)
  (trans (norm-hadamards n) (sym (ℕ+-zero n)))
  where
  ℕ+-zero : ∀ n → n ℕ+ 0 ≡ n
  ℕ+-zero zero    = refl
  ℕ+-zero (suc n) = cong suc (ℕ+-zero n)

-- A circuit multiplying by the sign of b is the oracle of any
-- exponent with the parities of b.

Sim-signs : {C : Circuit n} {b : Assign n → Bool} → Signs C b →
            (E : Poly n 0) → (∀ z → b z ≡ boolᴾ E z) →
            Sim (applyᴬ C) (Oᴾ E) 0
Sim-signs {C = C} s E h = sim (λ ψ r → applyᴬ-resp C r)
  (λ ψ r z i → trans (signed s ψ r z i)
    (trans (cong (λ t → sgn t * ψ z i) (h z))
           (sym (applyᴾ-Oᴾ′ E ψ r z i))))

-- So the circuit of a list of monomials is the oracle of their sum.

oracle-≋ : (ts : List (Term n)) (E : Poly n 0) →
           (∀ z → sumᵇ ts z ≡ boolᴾ E z) → ⟦ oracle ts ⟧ ≋ Oᴾ E
oracle-≋ ts E h =
  Sim-≋ (oracle ts) (Oᴾ E) (Sim-signs (Signs-oracle ts) E h) (norm-oracle ts)

-- Such a circuit conjugated by X^s is the oracle of the shifted
-- exponent, with the four Hadamards of each X in its normalisation.

private
  xor-back : ∀ a b → (a xor b) xor b ≡ a
  xor-back false false = refl
  xor-back false true  = refl
  xor-back true  false = refl
  xor-back true  true  = refl

Sim-shifted : (s : Assign n) {C : Circuit n} {b : Assign n → Bool} →
              Signs C b → (E : Poly n 0) → (∀ z → b z ≡ boolᴾ E z) →
              Sim (applyᴬ (flips s ++ (C ++ flips s))) (Oᴾ (shiftᴾ s E))
                  (norm (flips s) ℕ+ norm (flips s))
Sim-shifted s {C} {b} sC E h = sim
  (λ ψ r → applyᴬ-resp (flips s ++ (C ++ flips s)) r)
  (λ ψ r z i → trans (cong (λ F → F z i) (applyᴬ-++ (flips s) (C ++ flips s) ψ))
    (trans (cong (λ F → F z i) (applyᴬ-++ C (flips s) (applyᴬ (flips s) ψ)))
      (trans (applyᴬ-flips s (applyᴬ C (applyᴬ (flips s) ψ))
                (applyᴬ-resp C (applyᴬ-resp (flips s) r)) z i)
        (trans (scale-map Ns (signed sC (applyᴬ (flips s) ψ)
                                (applyᴬ-resp (flips s) r) (z ⊕ᵃ s)) i)
          (trans (scale-map Ns (λ l → cong (sgn (b (z ⊕ᵃ s)) *_)
                   (trans (applyᴬ-flips s ψ r (z ⊕ᵃ s) l)
                          (scale-map Ns (r _ z (λ j → xor-back (z j) (s j)))
                                     l)))
                 i)
            (trans (scale-map Ns (λ l → sym (scale-·ᴬ Ns (sgn (b (z ⊕ᵃ s)))
                                                     (ψ z) l)) i)
              (trans (scale-+ Ns Ns (sgn (b (z ⊕ᵃ s)) ·ᴬ ψ z) i)
                (scale-map (Ns ℕ+ Ns) (λ l → trans
                  (cong (λ t → sgn t * ψ z l)
                        (trans (h (z ⊕ᵃ s)) (sym (bool-shiftᴾ s E z))))
                  (sym (applyᴾ-Oᴾ′ (shiftᴾ s E) ψ r z l))) i))))))))
  where
  Ns : ℕ
  Ns = norm (flips s)
