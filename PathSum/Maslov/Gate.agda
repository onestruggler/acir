------------------------------------------------------------------------
-- Presentations of groups
--
-- The relative-phase Toffoli gate on any three wires (Amy, QPL 2018,
-- section 5.2; Maslov, Phys. Rev. A 93, 2016, the paper's [23])
--
-- The gate is the Toffoli gate's Hadamard-sandwiched doubly controlled
-- Z with the three T gates on the controls dropped and one CNOT fewer:
--
--    rtof c₁ c₂ t = H t ; T t ; CNOT c₂ t ; T† t ; CNOT c₁ t ; T t ;
--                   CNOT c₂ t ; T† t ; H t
--
-- over {H, CNOT, T, T†} (T = R_3), four T gates, two Hadamards and
-- three CNOTs, with controls c₁, c₂ and target t any wires of an
-- n-wire circuit other than t (c₁ = c₂ is allowed and gives a CNOT up
-- to a phase), for every n and every M = 3 + M₀.  This is the
-- three-CNOT, four-T gate that circuit libraries ship as the
-- relative-phase ("simplified", Margolus-type) Toffoli gate and
-- attribute to [23]: it is the dashed box of figure 3 of [23]
-- (Maslov, arXiv:1508.03273), whose printed matrix is the relative
-- phase below.
--
-- The theorem is that it computes the Toffoli function up to a
-- relative phase, computed exactly (rtof-up-to):
--
--    |x⟩ ↦ i^(x_c₁ x_c₂) (-1)^(x_c₁ x_t) |x[t ≔ x_t ⊕ x_c₁ x_c₂]⟩,
--
-- the phase ½ x_c₁ x_t + ¼ x_c₁ x_c₂ (rtof-phase) being read before the
-- gate.  So its path-sum is ≋ the path-sum without path variables whose
-- phase polynomial is ½ x_c₁ x_t + ¼ x_c₁ x_c₂ and whose output on t
-- is the lift of x_t ⊕ x_c₁ x_c₂ (rtof-spec), and it is not the Toffoli
-- gate (rtof-not-toffoli: at x_c₁ = x_t = 1, x_c₂ = 0 its amplitude is
-- -1 where Toffoli's is 1).  As an operator it is Toffoli · CZ(c₁,t) ·
-- CS(c₁,c₂), a diagonal of phases followed by the Toffoli permutation.
--
-- The route is PathSum.Toffoli's: the circuit's amplitudes, path by
-- path.  The Hadamards allocate y₁ (the first) and y₂ (the second, the
-- head variable).  Along a path t reads y₁, then y₁ ⊕ x₂, y₁ ⊕ x₂ ⊕ x₁
-- and y₁ ⊕ x₁ (x₁, x₂ for x_c₁, x_c₂), and y₂ at the end; the phase is
-- ½ x_t y₁ from the first Hadamard, ½ (y₁ ⊕ x₁) y₂ from the second,
-- and ⅛ (y₁ - (y₁ ⊕ x₂) + (y₁ ⊕ x₂ ⊕ x₁) - (y₁ ⊕ x₁)) = ½ x₁ x₂ y₁ - ¼
-- x₁ x₂ from the T gates (Along.exact, rtof-path-phase: the gate's
-- path-sum, stated through its values).  Where the Toffoli gate's T
-- gates leave ½ x₁ x₂ y₁ exactly, these leave the -¼ x₁ x₂ of the
-- missing controls' T gates as well, and the last CNOT onto t being
-- missing makes the second Hadamard read y₁ ⊕ x₁, adding ½ x₁ y₂.
-- Modulo 1 the phase is ½ y₁ (y₂ ⊕ x_t ⊕ x₁ x₂) + ½ x₁ y₂ - ¼ x₁ x₂,
-- so the sum over y₁ is 2 or 0 according as y₂ = x_t ⊕ x₁ x₂ -- the
-- Toffoli function again -- and the surviving path carries the phase
-- ½ x₁ (x_t ⊕ x₁ x₂) - ¼ x₁ x₂ ≡ ½ x₁ x_t + ¼ x₁ x₂ (PathSum.Maslov.
-- Arith).  The circuit is read through a simulation
-- (PathSum.CRK.Path.Sim), so no state of its run is computed or
-- compared, and no closed instance is evaluated.
--
-- Cancellation.  The circuit is its own mirror image with every gate
-- inverted, so it is its own inverse (rtof-†, by computation with
-- PathSum.CRK.Adjoint's _†), and the gate followed by its inverse
-- computes the identity exactly (rtof-rtof): its phases at x and at the
-- Toffoli image of x add up to ½ x₁ (x_t + x_t ⊕ x₁ x₂) + ½ x₁ x₂ ≡ 0
-- (rtof-cancel).  More generally (rtof-sandwich) the gate, any circuit
-- D that computes a function G up to a phase ψ and leaves the values
-- of c₁, c₂ and t alone, and the gate's inverse, compute
-- x ↦ T(G(T x)) up to ψ(T x), T the Toffoli function: the relative
-- phases cancel, which is what a decomposition into relative-phase
-- Toffoli gates relies on.  (Stated with PathSum.RelativePhase's
-- records: the ≋ form of a composite of concrete circuits is best
-- avoided, see PathSum.Toffoli.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Maslov.Gate (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-identityʳ; *-zeroʳ)
open import Data.List.Base using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (scale-exp)
open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; same)
open import PathSum.Base using (PathSum; phase)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; computes-≗; ≋classical⇒computes; none; setWire)
open import PathSum.Compose.Sum M₀ using (if-cong; rot-if)
open import PathSum.CRK.Adjoint M using (_†)
open import PathSum.CRK.Path M₀ using
  (H; CNOT; R; R†; Circuit; ⟦_⟧; norm; init; Sim; end; R-sim; R†-sim;
   CNOT-sim; H-sim; sim-outBit; sim-phase; amp-sim)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _·ᴬ_; _≐_; Σᴮ; Σᴮ-cong; zpow; zpow-anti; zpow0-at-0; 0ᶠ; rot)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Maslov.Arith M₀ using
  (R-bracket; back-tᴿ; tidyᴿ; ⅛-split; arrange; path-phaseᴿ; survive;
   cancelᴿ; pairʳ; outerʳ; select-if)
open import PathSum.Polynomial using (Poly; x[_]; eval; _+ᴾ_; _·ᴾ_)
open import PathSum.Polynomial.Boolean using (var; _∧ᵉ_; liftᵉ; eval-liftᵉ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-·ᴾ)
open import PathSum.Reduction M using (⅛; ¼; ½)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-≡; ≡ᴺ-trans; zpow-≡ᴺ; _computes_up-to_; computing-up-to;
   up-to-≗; up-to-phase; up-to⇒computes; up-to-exact; phased;
   up-to⇒≋phased; ⟦++⟧-up-to; sandwich)
open import PathSum.Toffoli.Arith M₀ using (scale-two; select)
open import PathSum.Toffoli.Gate M₀ using
  (toffoli; toffoli-involutive; toffoliᵉ; toffoliˢ; fun-toffoliˢ)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The circuit and its specification

-- Controls c₁ and c₂, target t (T = R 3, T† = R† 3).  The head of the
-- list is applied first.

rtof : (c₁ c₂ t : Fin n) → c₁ ≢ t → c₂ ≢ t → Circuit n
rtof c₁ c₂ t c₁≢t c₂≢t =
  H t ∷ R 3 t ∷ CNOT c₂ t c₂≢t ∷ R† 3 t ∷ CNOT c₁ t c₁≢t ∷ R 3 t ∷
  CNOT c₂ t c₂≢t ∷ R† 3 t ∷ H t ∷ []

-- The relative phase, a numerator over 2^M: ½ x_c₁ x_t + ¼ x_c₁ x_c₂,
-- that is (-1)^(x_c₁ x_t) i^(x_c₁ x_c₂).

rtof-phase : (c₁ c₂ t : Fin n) → Assign n → ℤ
rtof-phase c₁ c₂ t x = ½ * [ x c₁ ∧ x t ]ᶻ + ¼ * [ x c₁ ∧ x c₂ ]ᶻ

-- The same as a phase polynomial, and the specification:
-- |x⟩ ↦ ζ^(½ x_c₁ x_t + ¼ x_c₁ x_c₂) |x[t ≔ x_t ⊕ x_c₁ x_c₂]⟩.

rtofᴾ : (c₁ c₂ t : Fin n) → Poly n 0
rtofᴾ c₁ c₂ t = (½ ·ᴾ liftᵉ (var x[ c₁ ] ∧ᵉ var x[ t ]))
                +ᴾ (¼ ·ᴾ liftᵉ (var x[ c₁ ] ∧ᵉ var x[ c₂ ]))

eval-rtofᴾ : (c₁ c₂ t : Fin n) (x : Assign n) →
             eval (rtofᴾ c₁ c₂ t) x none ≡ rtof-phase c₁ c₂ t x
eval-rtofᴾ c₁ c₂ t x = trans
  (eval-+ᴾ (½ ·ᴾ liftᵉ (var x[ c₁ ] ∧ᵉ var x[ t ]))
           (¼ ·ᴾ liftᵉ (var x[ c₁ ] ∧ᵉ var x[ c₂ ])) x none)
  (cong₂ _+_
    (trans (eval-·ᴾ ½ (liftᵉ (var x[ c₁ ] ∧ᵉ var x[ t ])) x none)
           (cong (½ *_) (eval-liftᵉ (var x[ c₁ ] ∧ᵉ var x[ t ]) x none)))
    (trans (eval-·ᴾ ¼ (liftᵉ (var x[ c₁ ] ∧ᵉ var x[ c₂ ])) x none)
           (cong (¼ *_) (eval-liftᵉ (var x[ c₁ ] ∧ᵉ var x[ c₂ ]) x none))))

rtofˢ : (c₁ c₂ t : Fin n) → PathSum n 0 0
rtofˢ c₁ c₂ t = phased (rtofᴾ c₁ c₂ t) (setWire t (liftᵉ (toffoliᵉ c₁ c₂ t)))

-- The phase reads only c₁, c₂ and t.

phase-at : (c₁ c₂ t : Fin n) (y : Assign n) {a b c : Bool} →
           y c₁ ≡ a → y c₂ ≡ b → y t ≡ c →
           rtof-phase c₁ c₂ t y ≡ ½ * [ a ∧ c ]ᶻ + ¼ * [ a ∧ b ]ᶻ
phase-at c₁ c₂ t y refl refl refl = refl


------------------------------------------------------------------------
-- The circuit along one path

-- What remains of the phase along a path once y₁'s term is set apart,
-- as a function of y₂ = b.

rest : (c₁ c₂ : Fin n) → Assign n → Bool → ℤ
rest c₁ c₂ x b = ½ * [ x c₁ ∧ b ]ᶻ - ¼ * [ x c₁ ∧ x c₂ ]ᶻ

-- Along the path Y, at the input x.  Y zero is y₂, the second
-- Hadamard's variable, and Y (suc zero) is y₁, the first's.

private
  module Along {n : ℕ} {c₁ c₂ t : Fin n} (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t)
               (x : Assign n) (Y : Assign 2) where

    private
      x₁ x₂ xₜ y₁ y₂ : Bool
      x₁ = x c₁
      x₂ = x c₂
      xₜ = x t
      y₁ = Y (suc zero)
      y₂ = Y zero

      -- What t reads between the Hadamards, after each CNOT.

      v₂ v₃ v₄ : Bool
      v₂ = y₁ xor x₂
      v₃ = v₂ xor x₁
      v₄ = v₃ xor x₂

      -- Only t is ever written: a CNOT onto t from a control c adds x_c.

      cnot : (c : Fin n) → c ≢ t → (γ : Bool) →
             ∀ u → ((x [ t ≔ γ ]) [ t ≔ (x [ t ≔ γ ]) t xor (x [ t ≔ γ ]) c ])
                     u ≡ (x [ t ≔ γ xor x c ]) u
      cnot c c≢t γ u =
        trans (cong (λ b → ((x [ t ≔ γ ]) [ t ≔ b ]) u)
                    (cong₂ _xor_ (≔-here x t γ) (≔-there x γ c≢t)))
              (≔-≔ x t γ (γ xor x c) u)

    -- The phase value after the first Hadamard (E₁), after each phase
    -- gate, and after the second Hadamard (E₆).

    E₁ E₂ E₃ E₄ E₅ E₆ : ℤ
    E₁ = 0ℤ + ½ * [ xₜ ∧ y₁ ]ᶻ
    E₂ = E₁ + ⅛ * [ y₁ ]ᶻ
    E₃ = E₂ - ⅛ * [ v₂ ]ᶻ
    E₄ = E₃ + ⅛ * [ v₃ ]ᶻ
    E₅ = E₄ - ⅛ * [ v₄ ]ᶻ
    E₆ = E₅ + ½ * [ v₄ ∧ y₂ ]ᶻ

    -- The simulation, gate by gate: the wires read x except on t, which
    -- reads y₁, v₂, v₃, v₄ between the Hadamards and y₂ at the end.

    simulation : Sim x (x [ t ≔ Y zero ]) E₆ (rtof c₁ c₂ t c₁≢t c₂≢t)
                     init Y x 0ℤ
    simulation =
      H-sim {e₁ = E₁} refl (λ _ → refl) refl
      (R-sim {e₁ = E₂} (≔-here x t y₁) refl
      (CNOT-sim (cnot c₂ c₂≢t y₁)
      (R†-sim {e₁ = E₃} (≔-here x t v₂) refl
      (CNOT-sim (cnot c₁ c₁≢t v₂)
      (R-sim {e₁ = E₄} (≔-here x t v₃) refl
      (CNOT-sim (cnot c₂ c₂≢t v₃)
      (R†-sim {e₁ = E₅} (≔-here x t v₄) refl
      (H-sim {e₁ = E₆} (≔-here x t v₄) (λ u → ≔-≔ x t v₄ (Y zero) u) refl
      (end (λ _ → refl) refl)))))))))

    -- The phase: ½ x_t y₁ + ½ x₁ x₂ y₁ - ¼ x₁ x₂ + ½ (y₁ ⊕ x₁) y₂.

    exact : E₆ ≡ ½ * [ x t ∧ Y (suc zero) ]ᶻ
                 + ½ * [ (x c₁ ∧ x c₂) ∧ Y (suc zero) ]ᶻ
                 - ¼ * [ x c₁ ∧ x c₂ ]ᶻ
                 + ½ * [ (Y (suc zero) xor x c₁) ∧ Y zero ]ᶻ
    exact =
      trans (tidyᴿ ½ ⅛ [ xₜ ∧ y₁ ]ᶻ [ v₄ ∧ y₂ ]ᶻ [ y₁ ]ᶻ [ v₂ ]ᶻ [ v₃ ]ᶻ
                   [ v₄ ]ᶻ)
        (trans (cong₂ (λ u w → ½ * [ xₜ ∧ y₁ ]ᶻ + ½ * [ u ∧ y₂ ]ᶻ + w)
                      (back-tᴿ y₁ x₁ x₂)
                      (trans (cong (⅛ *_) (R-bracket y₁ x₁ x₂))
                             (⅛-split [ (x₁ ∧ x₂) ∧ y₁ ]ᶻ [ x₁ ∧ x₂ ]ᶻ)))
               (arrange (½ * [ xₜ ∧ y₁ ]ᶻ) (½ * [ (y₁ xor x₁) ∧ y₂ ]ᶻ)
                        (½ * [ (x₁ ∧ x₂) ∧ y₁ ]ᶻ) (¼ * [ x₁ ∧ x₂ ]ᶻ)))

    -- Modulo 1: ½ y₁ (y₂ ⊕ x_t ⊕ x₁ x₂), plus the rest.

    phase-zpow : zpow E₆ ≐
                 zpow (½ * [ Y (suc zero) ∧
                             (Y zero xor (x t xor (x c₁ ∧ x c₂))) ]ᶻ
                       + rest c₁ c₂ x (Y zero))
    phase-zpow = zpow-≡ᴺ (≡ᴺ-trans (≡ᴺ-≡ exact)
      (path-phaseᴿ (x t) (x c₁) (x c₂) (Y (suc zero)) (Y zero)))


------------------------------------------------------------------------
-- The gate's path-sum, path by path

-- Along the path Y the outputs are x[t ≔ y₂] and the phase is
-- ½ x_t y₁ + ½ x_c₁ x_c₂ y₁ - ¼ x_c₁ x_c₂ + ½ (y₁ ⊕ x_c₁) y₂: the
-- path-sum of the circuit is
--
--    |x⟩ ↦ 1/√2² Σ_{y₁,y₂}
--            e^(2πi (½ x_t y₁ + ½ x_c₁ x_c₂ y₁ - ¼ x_c₁ x_c₂
--                    + ½ (y₁ ⊕ x_c₁) y₂)) |x[t ≔ y₂]⟩.

rtof-outputs : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t)
               (x : Assign n) (Y : Assign 2) →
               ∀ u → outBit ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ⟧ x Y u ≡
                     (x [ t ≔ Y zero ]) u
rtof-outputs c₁ c₂ t c₁≢t c₂≢t x Y =
  sim-outBit (rtof c₁ c₂ t c₁≢t c₂≢t) x Y (Along.simulation c₁≢t c₂≢t x Y)

rtof-path-phase : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t)
                  (x : Assign n) (Y : Assign 2) →
                  eval (phase ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ⟧) x Y ≡
                  ½ * [ x t ∧ Y (suc zero) ]ᶻ
                  + ½ * [ (x c₁ ∧ x c₂) ∧ Y (suc zero) ]ᶻ
                  - ¼ * [ x c₁ ∧ x c₂ ]ᶻ
                  + ½ * [ (Y (suc zero) xor x c₁) ∧ Y zero ]ᶻ
rtof-path-phase c₁ c₂ t c₁≢t c₂≢t x Y =
  trans (sim-phase (rtof c₁ c₂ t c₁≢t c₂≢t) x Y
                   (Along.simulation c₁≢t c₂≢t x Y))
        (Along.exact c₁≢t c₂≢t x Y)

-- What the path Y contributes to the amplitude from x to z: ζ to
-- ½ y₁ q + rest(y₂) if the output x[t ≔ y₂] is z, q being
-- y₂ ⊕ x_t ⊕ x_c₁ x_c₂.

pathsumᴿ : (c₁ c₂ t : Fin n) → Assign n → Assign n → Assign 2 → Amp
pathsumᴿ c₁ c₂ t x z Y =
  if same (x [ t ≔ Y zero ]) z
  then zpow (½ * [ Y (suc zero) ∧ (Y zero xor (x t xor (x c₁ ∧ x c₂))) ]ᶻ
             + rest c₁ c₂ x (Y zero))
  else 0ᴬ

rtof-amp : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t)
           (x z : Assign n) →
           amp ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ⟧ x z ≐ Σᴮ (pathsumᴿ c₁ c₂ t x z)
rtof-amp c₁ c₂ t c₁≢t c₂≢t x z =
  amp-sim (rtof c₁ c₂ t c₁≢t c₂≢t) x z (λ Y → x [ t ≔ Y zero ])
          (Along.E₆ c₁≢t c₂≢t x) (Along.simulation c₁≢t c₂≢t x)
  ∙ Σᴮ-cong {k = 2}
      {f = λ Y → if same (x [ t ≔ Y zero ]) z
                 then zpow (Along.E₆ c₁≢t c₂≢t x Y) else 0ᴬ}
      {g = pathsumᴿ c₁ c₂ t x z}
      (λ Y → if-cong {p = same (x [ t ≔ Y zero ]) z} refl
                     (Along.phase-zpow c₁≢t c₂≢t x Y))

-- Summed: 2 ζ^rest(r) at the Toffoli function's value, r = x_t ⊕ x_c₁
-- x_c₂, and 0 elsewhere.

Σ-pathsumᴿ : (c₁ c₂ t : Fin n) (x z : Assign n) →
             Σᴮ (pathsumᴿ c₁ c₂ t x z) ≐
             (+ 2) ·ᴬ (if same (toffoli c₁ c₂ t x) z
                       then zpow (rest c₁ c₂ x (x t xor (x c₁ ∧ x c₂)))
                       else 0ᴬ)
Σ-pathsumᴿ c₁ c₂ t x z i =
  trans (cong₂ _+_ (pairʳ (s true) (not r) (rest c₁ c₂ x true) i)
                   (pairʳ (s false) r (rest c₁ c₂ x false) i))
    (trans (outerʳ r (s true) (s false) (rest c₁ c₂ x true)
                   (rest c₁ c₂ x false) i)
           (cong₂ (λ b e → ((+ 2) ·ᴬ (if b then zpow e else 0ᴬ)) i)
                  (select s r) (select-if (rest c₁ c₂ x) r)))
  where
  r : Bool
  r = x t xor (x c₁ ∧ x c₂)

  s : Bool → Bool
  s b = same (x [ t ≔ b ]) z


------------------------------------------------------------------------
-- The theorem

-- The gate computes the Toffoli function up to the relative phase
-- ½ x_c₁ x_t + ¼ x_c₁ x_c₂: its unnormalised amplitude from x to z is
-- √2² ζ^(½ x_c₁ x_t + ¼ x_c₁ x_c₂) when z = x[t ≔ x_t ⊕ x_c₁ x_c₂],
-- and 0 otherwise.

rtof-up-to : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t) →
             ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ⟧
               computes toffoli c₁ c₂ t up-to rtof-phase c₁ c₂ t
rtof-up-to c₁ c₂ t c₁≢t c₂≢t = computing-up-to λ x z →
  rtof-amp c₁ c₂ t c₁≢t c₂≢t x z
  ∙ Σ-pathsumᴿ c₁ c₂ t x z
  ∙ (λ i → cong ((+ 2) *_)
       ((if-cong {p = same (toffoli c₁ c₂ t x) z} refl
                 (zpow-≡ᴺ (survive (x t) (x c₁) (x c₂)))
         ∙ ≐-sym (rot-if (same (toffoli c₁ c₂ t x) z)
                         (rtof-phase c₁ c₂ t x) 0ℤ)) i))
  ∙ scale-two (rot (rtof-phase c₁ c₂ t x) (δ (toffoli c₁ c₂ t x) z))
  ∙ scale-exp {2} {norm (rtof c₁ c₂ t c₁≢t c₂≢t)}
              (rot (rtof-phase c₁ c₂ t x) (δ (toffoli c₁ c₂ t x) z)) refl

-- So its path-sum is the explicit one: a diagonal phase, then the
-- Toffoli permutation.

rtof-spec : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t) →
            ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ⟧ ≋ rtofˢ c₁ c₂ t
rtof-spec c₁ c₂ t c₁≢t c₂≢t =
  up-to⇒≋phased _ (rtofᴾ c₁ c₂ t) (setWire t (liftᵉ (toffoliᵉ c₁ c₂ t)))
    (up-to-phase _ (λ x → ≡ᴺ-≡ (sym (eval-rtofᴾ c₁ c₂ t x)))
      (up-to-≗ _ (λ x w → sym (fun-toffoliˢ c₁ c₂ t x w))
        (rtof-up-to c₁ c₂ t c₁≢t c₂≢t)))

-- And the phase is not trivial: at x_c₁ = x_t = 1, x_c₂ = 0 the gate's
-- amplitude to the Toffoli image is -√2², the Toffoli gate's √2²
-- (PathSum.RelativePhase.up-to-exact reads both off).

private
  1≢-1 : ¬ (1ℤ ≡ - 1ℤ)
  1≢-1 ()

rtof-not-toffoli : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t) →
                   c₁ ≢ c₂ → ¬ (⟦ rtof c₁ c₂ t c₁≢t c₂≢t ⟧ ≋ toffoliˢ c₁ c₂ t)
rtof-not-toffoli {n} c₁ c₂ t c₁≢t c₂≢t c₁≢c₂ eq =
  1≢-1 (trans (sym zpow0-at-0)
              (trans (flip 0ᶠ) (cong -_ zpow0-at-0)))
  where
  x : Assign n
  x = (λ _ → true) [ c₂ ≔ false ]

  φ : ℤ
  φ = rtof-phase c₁ c₂ t x

  exactly : ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ⟧ computes toffoli c₁ c₂ t
  exactly = computes-≗ _ (fun-toffoliˢ c₁ c₂ t)
    (≋classical⇒computes _ (setWire t (liftᵉ (toffoliᵉ c₁ c₂ t))) eq)

  value : φ + 0ℤ ≡ 0ℤ + ½
  value = trans
    (cong (_+ 0ℤ) (phase-at c₁ c₂ t x
      (≔-there (λ _ → true) false c₁≢c₂)
      (≔-here (λ _ → true) c₂ false)
      (≔-there (λ _ → true) false (λ e → c₂≢t (sym e)))))
    (trans (cong₂ (λ a b → a + b + 0ℤ) (*-identityʳ ½) (*-zeroʳ ¼))
      (trans (+-identityʳ (½ + 0ℤ))
        (trans (+-identityʳ ½) (sym (+-identityˡ ½)))))

  flip : zpow 0ℤ ≐ (λ i → - zpow 0ℤ i)
  flip = up-to-exact _ exactly (rtof-up-to c₁ c₂ t c₁≢t c₂≢t) x
         ∙ (λ i → trans (cong (λ e → zpow e i) value) (zpow-anti 0ℤ i))


------------------------------------------------------------------------
-- The gate undone

-- The circuit is its own inverse, gate for gate.

rtof-† : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t) →
         rtof c₁ c₂ t c₁≢t c₂≢t † ≡ rtof c₁ c₂ t c₁≢t c₂≢t
rtof-† c₁ c₂ t c₁≢t c₂≢t = refl

-- The relative phases at x and at the Toffoli image of x cancel.

rtof-cancel : (c₁ c₂ t : Fin n) → c₁ ≢ t → c₂ ≢ t → (x : Assign n) →
              rtof-phase c₁ c₂ t x + rtof-phase c₁ c₂ t (toffoli c₁ c₂ t x)
              ≡ᴺ 0ℤ
rtof-cancel c₁ c₂ t c₁≢t c₂≢t x = ≡ᴺ-trans
  (≡ᴺ-≡ (cong (λ e → rtof-phase c₁ c₂ t x + e)
    (phase-at c₁ c₂ t (toffoli c₁ c₂ t x)
      (≔-there x (x t xor (x c₁ ∧ x c₂)) c₁≢t)
      (≔-there x (x t xor (x c₁ ∧ x c₂)) c₂≢t)
      (≔-here x t (x t xor (x c₁ ∧ x c₂))))))
  (cancelᴿ (x t) (x c₁) (x c₂))

-- So the gate followed by its inverse computes the identity, exactly.

rtof-rtof : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t) →
            ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ++ rtof c₁ c₂ t c₁≢t c₂≢t † ⟧
              computes (λ x → x)
rtof-rtof c₁ c₂ t c₁≢t c₂≢t =
  computes-≗ _ (toffoli-involutive c₁ c₂ t c₁≢t c₂≢t)
    (up-to⇒computes _
      (⟦++⟧-up-to (rtof c₁ c₂ t c₁≢t c₂≢t) (rtof c₁ c₂ t c₁≢t c₂≢t †)
                  (rtof-up-to c₁ c₂ t c₁≢t c₂≢t)
                  (rtof-up-to c₁ c₂ t c₁≢t c₂≢t))
      (rtof-cancel c₁ c₂ t c₁≢t c₂≢t))

-- More generally: around any circuit D that computes G up to ψ and
-- leaves the values of c₁, c₂ and t alone, the gate and its inverse
-- contribute the Toffoli permutation on either side and no phase.

rtof-sandwich : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t)
                (D : Circuit n) {G : Assign n → Assign n}
                {ψ : Assign n → ℤ} → ⟦ D ⟧ computes G up-to ψ →
                (∀ x → G x c₁ ≡ x c₁) → (∀ x → G x c₂ ≡ x c₂) →
                (∀ x → G x t ≡ x t) →
                ⟦ rtof c₁ c₂ t c₁≢t c₂≢t ++ D ++ rtof c₁ c₂ t c₁≢t c₂≢t † ⟧
                  computes (λ x → toffoli c₁ c₂ t (G (toffoli c₁ c₂ t x)))
                  up-to (λ x → ψ (toffoli c₁ c₂ t x))
rtof-sandwich c₁ c₂ t c₁≢t c₂≢t D {G} cD g₁ g₂ gₜ =
  sandwich (rtof c₁ c₂ t c₁≢t c₂≢t) D (rtof c₁ c₂ t c₁≢t c₂≢t †)
           (rtof-up-to c₁ c₂ t c₁≢t c₂≢t) cD (rtof-up-to c₁ c₂ t c₁≢t c₂≢t)
           cancel
  where
  cancel : ∀ x → rtof-phase c₁ c₂ t x
                 + rtof-phase c₁ c₂ t (G (toffoli c₁ c₂ t x)) ≡ᴺ 0ℤ
  cancel x = ≡ᴺ-trans
    (≡ᴺ-≡ (cong (λ e → rtof-phase c₁ c₂ t x + e)
      (phase-at c₁ c₂ t (G (toffoli c₁ c₂ t x))
        (trans (g₁ (toffoli c₁ c₂ t x))
               (≔-there x (x t xor (x c₁ ∧ x c₂)) c₁≢t))
        (trans (g₂ (toffoli c₁ c₂ t x))
               (≔-there x (x t xor (x c₁ ∧ x c₂)) c₂≢t))
        (trans (gₜ (toffoli c₁ c₂ t x))
               (≔-here x t (x t xor (x c₁ ∧ x c₂)))))))
    (cancelᴿ (x t) (x c₁) (x c₂))
