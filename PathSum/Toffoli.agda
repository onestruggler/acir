------------------------------------------------------------------------
-- Presentations of groups
--
-- The Toffoli gate on any three wires (Amy, QPL 2018, example 3.3 and
-- section 5.2)
--
-- Section 5.2 builds n-bit Toffoli gates out of Clifford+T Toffoli
-- gates on three of the wires.  Here is that building block, for every
-- number n of wires and every M = 3 + M₀: tof c₁ c₂ t is the seven-T
-- circuit of Nielsen and Chuang's figure 4.9, with the T† and S on the
-- second control merged into one T, over {H, CNOT, T, T†} (T = R_3), with
-- controls c₁, c₂ and target t any three distinct wires -- the circuit
-- ToffoliC of PathSum.Examples.Toffoli, which is proved there for
-- n = 3 and M = 3 only, by computation, here placed on arbitrary
-- wires.  The theorem is that it computes the Toffoli function
--
--    |x⟩ ↦ |x[t ≔ x_t ⊕ x_c₁ x_c₂]⟩                      (tof-computes)
--
-- that is, that its path-sum is ≋ the classical path-sum toffoliˢ:
-- phase 0, no path variables, no normalisation, the outputs the inputs
-- except on t, which reads the lift of x_t ⊕ x_c₁ x_c₂ (tof-spec).
--
-- The route is the circuit's amplitudes, path by path, not the paper's
-- rewriting.  Its two Hadamards on t allocate y₁ (the first) and y₂
-- (the second, which the circuit lists first, as the head variable).
-- Along a path the wires read x, except that between the Hadamards t
-- reads y₁ ⊕ x₂, then ⊕ x₁, ⊕ x₂, ⊕ x₁ again (x₁, x₂ for x_c₁, x_c₂);
-- after the second Hadamard t reads y₂, and the two CNOTs onto c₂
-- cancel.  The phase is ½ x_t y₁ (first Hadamard) + ½ y₁ y₂ (second)
-- plus, from the seven T and T†, 2^(M-3) times
--
--    x₂ + x₁ - (x₂ ⊕ x₁) - (y₁ ⊕ x₂) + (y₁ ⊕ x₂ ⊕ x₁) - (y₁ ⊕ x₁) + y₁
--       = 4 x₁ x₂ y₁
--
-- (PathSum.Toffoli.Arith.T-bracket, an identity of integers at Boolean
-- points), which is ½ x₁ x₂ y₁.  So along every path the outputs are
-- x[t ≔ y₂] and the phase is exactly example 3.3's
--
--    ½ (x_t y₁ + x_c₁ x_c₂ y₁ + y₁ y₂)             (tof-outputs, tof-phase)
--
-- -- the paper's path-sum of the Toffoli gate, on any wires, stated
-- through its values (the polynomials themselves are never computed).
-- Modulo 1 that phase is ½ · (y₁ ∧ (y₂ ⊕ x_t ⊕ x₁x₂)) (Arith.zpow-½³),
-- so summing over y₁ gives 2 when y₂ = x_t ⊕ x₁x₂ and 0 otherwise --
-- the paper's [HH] step, done on amplitudes -- and the one surviving
-- path contributes 2 = √2², the two units of normalisation the paper's
-- [Elim] step removes (PathSum.Toffoli.Gate.Σ-pathsum, Arith.scale-two).
--
-- Why amplitudes rather than the rules of figure 2.  Carried out
-- symbolically on arbitrary wires, the paper's [HH]/[Elim] derivation
-- has to identify polynomials after substitution coefficient by
-- coefficient (through PathSum.Mobius), for an n-variable phase whose
-- shape depends on which wires c₁, c₂ and t are.  Along one path,
-- instead, every quantity is a Boolean or an integer: the case analyses
-- are on at most four Booleans, and the integer identities hold by the
-- laws of ℤ with 2^(M-3) and ½ symbolic.  The price is that the
-- derivation itself is not reproduced here; it is, for the closed
-- three-qubit instance, in PathSum.Examples.Toffoli.
--
-- The circuit is read through a simulation (PathSum.CRK.Path.Sim): the
-- wire values and the phase value before each of its fifteen gates,
-- along an arbitrary path Y (Along.simulation).  Its consequences are
-- drawn by PathSum.CRK.Path's sim-outBit, sim-phase and amp-sim, which
-- are proved once for every circuit; so no state of the circuit's run
-- is ever computed or compared, and no closed instance is evaluated.
--
-- Finally, as a first use of PathSum.Classical's composition lemmas
-- on this gate, two Toffoli gates on the same wires compute the
-- identity (tof-tof).  Section 5.2's n-bit Toffoli gates are not
-- built here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Toffoli (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_; _-_; _*_)
open import Data.List.Base using (_++_)
open import Data.Nat.Base using (_∸_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (scale-exp)
open import PathSum.Assign using ([_]ᶻ; _[_≔_]; same)
open import PathSum.Base using (phase)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; computing; computes-≗; computes⇒≋classical; setWire;
   ⟦++⟧-computes)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.CRK.Path M₀ using
  (⟦_⟧; norm; init; Sim; end; R-sim; R†-sim; CNOT-sim; H-sim;
   sim-outBit; sim-phase; amp-sim)
open import PathSum.Cyclotomic M₀ using (Amp; 0ᴬ; _≐_; Σᴮ; Σᴮ-cong; zpow)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Boolean using (liftᵉ)
open import PathSum.Reduction M using (½)
open import PathSum.Toffoli.Arith M₀ using
  (T-bracket; tidy; four-T; swap-last; zpow-½³; back-t; back-c₂;
   phase-bit; scale-two)
open import PathSum.Toffoli.Gate M₀ public using
  (tof; toffoli; toffoli-involutive; toffoliᵉ; toffoliˢ; fun-toffoliˢ;
   pathsum; Σ-pathsum)
open import PathSum.Toffoli.Gate M₀ using (module Wires)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)


------------------------------------------------------------------------
-- The circuit along one path

-- Along the path Y, at the input x.  Y zero is y₂, the second
-- Hadamard's variable, and Y (suc zero) is y₁, the first's.

module Along {n : ℕ} {c₁ c₂ t : Fin n} (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
             (c₂≢t : c₂ ≢ t) (x : Assign n) (Y : Assign 2) where

  open Wires c₁≢c₂ c₁≢t c₂≢t x

  private
    x₁ x₂ xₜ y₁ y₂ : Bool
    x₁ = x c₁
    x₂ = x c₂
    xₜ = x t
    y₁ = Y (suc zero)
    y₂ = Y zero

    -- What t reads between the Hadamards.

    v₂ v₄ v₆ v₈ : Bool
    v₂ = y₁ xor x₂
    v₄ = v₂ xor x₁
    v₆ = v₄ xor x₂
    v₈ = v₆ xor x₁

    T : ℤ
    T = pow (M ∸ 3)

  -- The phase value after the first Hadamard (E₁), after each phase
  -- gate, and after the second Hadamard (E₁₁); E₁₅ at the end.

  E₁ E₃ E₅ E₇ E₉ E₁₀ E₁₁ E₁₃ E₁₅ : ℤ
  E₁  = 0ℤ + ½ * [ xₜ ∧ y₁ ]ᶻ
  E₃  = E₁ - T * [ v₂ ]ᶻ
  E₅  = E₃ + T * [ v₄ ]ᶻ
  E₇  = E₅ - T * [ v₆ ]ᶻ
  E₉  = E₇ + T * [ v₈ ]ᶻ
  E₁₀ = E₉ + T * [ x₂ ]ᶻ
  E₁₁ = E₁₀ + ½ * [ v₈ ∧ y₂ ]ᶻ
  E₁₃ = E₁₁ - T * [ x₂ xor x₁ ]ᶻ
  E₁₅ = E₁₃ + T * [ x₁ ]ᶻ

  -- The simulation, gate by gate.  Between the Hadamards the wires
  -- read x₁ and x₂ on c₁ and c₂, and on t y₁, v₂, v₄, v₆, v₈; after
  -- the second Hadamard t reads y₂, and c₂ reads x₂ ⊕ x₁ and then x₂
  -- again.  At the end the wires read x, except t, which reads y₂.

  simulation : Sim x (x [ t ≔ Y zero ]) E₁₅ (tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t)
                   init Y x 0ℤ
  simulation =
    H-sim {e₁ = E₁} refl (w3-x y₁) refl
    (CNOT-sim (cnot-t c₂ x₁ x₂ y₁ x₂ (w3-c₂ x₁ x₂ y₁))
    (R†-sim {e₁ = E₃} (w3-t x₁ x₂ v₂) refl
    (CNOT-sim (cnot-t c₁ x₁ x₂ v₂ x₁ (w3-c₁ x₁ x₂ v₂))
    (R-sim {e₁ = E₅} (w3-t x₁ x₂ v₄) refl
    (CNOT-sim (cnot-t c₂ x₁ x₂ v₄ x₂ (w3-c₂ x₁ x₂ v₄))
    (R†-sim {e₁ = E₇} (w3-t x₁ x₂ v₆) refl
    (CNOT-sim (cnot-t c₁ x₁ x₂ v₆ x₁ (w3-c₁ x₁ x₂ v₆))
    (R-sim {e₁ = E₉} (w3-t x₁ x₂ v₈) refl
    (R-sim {e₁ = E₁₀} (w3-c₂ x₁ x₂ v₈) refl
    (H-sim {e₁ = E₁₁} (w3-t x₁ x₂ v₈) (h-t x₁ x₂ v₈ y₂ refl) refl
    (CNOT-sim (cnot-c₂ x₁ x₂ y₂)
    (R†-sim {e₁ = E₁₃} (w3-c₂ x₁ (x₂ xor x₁) y₂) refl
    (CNOT-sim (cnot-c₂ x₁ (x₂ xor x₁) y₂)
    (R-sim {e₁ = E₁₅} (w3-c₁ x₁ ((x₂ xor x₁) xor x₁) y₂) refl
    (end (λ u → trans (cong (λ β → w3 x₁ β y₂ u) (back-c₂ x₂ x₁))
                      (sym (w3-x y₂ u)))
         refl)))))))))))))))

  -- The phase: ½ x_t y₁ + ½ x₁ x₂ y₁ + ½ y₁ y₂, exactly.

  exact : E₁₅ ≡ ½ * [ x t ∧ Y (suc zero) ]ᶻ
                + ½ * [ (x c₁ ∧ x c₂) ∧ Y (suc zero) ]ᶻ
                + ½ * [ Y (suc zero) ∧ Y zero ]ᶻ
  exact = trans (tidy ½ T [ xₜ ∧ y₁ ]ᶻ [ v₈ ∧ y₂ ]ᶻ [ v₂ ]ᶻ [ v₄ ]ᶻ [ v₆ ]ᶻ
                      [ v₈ ]ᶻ [ x₂ ]ᶻ [ x₂ xor x₁ ]ᶻ [ x₁ ]ᶻ)
    (trans (cong₂ (λ q s → ½ * [ xₜ ∧ y₁ ]ᶻ + q + s)
                  (cong (λ v → ½ * [ v ∧ y₂ ]ᶻ) (back-t y₁ x₁ x₂))
                  (trans (cong (T *_) (T-bracket y₁ x₁ x₂))
                         (four-T [ (x₁ ∧ x₂) ∧ y₁ ]ᶻ)))
           (swap-last (½ * [ xₜ ∧ y₁ ]ᶻ) (½ * [ y₁ ∧ y₂ ]ᶻ)
                      (½ * [ (x₁ ∧ x₂) ∧ y₁ ]ᶻ)))

  -- Modulo 1: ½ · (y₁ ∧ (y₂ ⊕ x_t ⊕ x₁ x₂)).

  phase-zpow : zpow E₁₅ ≐
               zpow (½ * [ Y (suc zero) ∧
                           (Y zero xor (x t xor (x c₁ ∧ x c₂))) ]ᶻ)
  phase-zpow = zpow-≡ exact
    ∙ zpow-½³ (x t ∧ Y (suc zero)) ((x c₁ ∧ x c₂) ∧ Y (suc zero))
              (Y (suc zero) ∧ Y zero)
    ∙ zpow-≡ (cong (λ d → ½ * [ d ]ᶻ)
                   (phase-bit (x t) (x c₁ ∧ x c₂) (Y zero) (Y (suc zero))))


------------------------------------------------------------------------
-- The circuit's path-sum, path by path

-- Example 3.3 on any wires.  Along the path Y the outputs are
-- x[t ≔ y₂] and the phase is ½ x_t y₁ + ½ x_c₁ x_c₂ y₁ + ½ y₁ y₂: the
-- path-sum of the circuit is the paper's
--
--    |x⟩ ↦ 1/√2² Σ_{y₁,y₂} e^(2πi ½ (x_t y₁ + x_c₁ x_c₂ y₁ + y₁ y₂))
--                            |x[t ≔ y₂]⟩.

tof-outputs : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
              (c₂≢t : c₂ ≢ t) (x : Assign n) (Y : Assign 2) →
              ∀ u → outBit ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ x Y u ≡
                    (x [ t ≔ Y zero ]) u
tof-outputs c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x Y =
  sim-outBit (tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) x Y
             (Along.simulation c₁≢c₂ c₁≢t c₂≢t x Y)

tof-phase : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
            (c₂≢t : c₂ ≢ t) (x : Assign n) (Y : Assign 2) →
            eval (phase ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧) x Y ≡
            ½ * [ x t ∧ Y (suc zero) ]ᶻ
            + ½ * [ (x c₁ ∧ x c₂) ∧ Y (suc zero) ]ᶻ
            + ½ * [ Y (suc zero) ∧ Y zero ]ᶻ
tof-phase c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x Y =
  trans (sim-phase (tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) x Y
                   (Along.simulation c₁≢c₂ c₁≢t c₂≢t x Y))
        (Along.exact c₁≢c₂ c₁≢t c₂≢t x Y)

-- Its amplitude from x to z: over the four paths, ζ^(½ y₁ q) at the
-- paths whose output x[t ≔ y₂] is z, q being y₂ ⊕ x_t ⊕ x_c₁ x_c₂.

tof-amp : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
          (c₂≢t : c₂ ≢ t) (x z : Assign n) →
          amp ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ x z ≐
          Σᴮ (pathsum c₁ c₂ t x z)
tof-amp c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x z =
  amp-sim (tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) x z (λ Y → x [ t ≔ Y zero ])
          (Along.E₁₅ c₁≢c₂ c₁≢t c₂≢t x)
          (Along.simulation c₁≢c₂ c₁≢t c₂≢t x)
  ∙ Σᴮ-cong {k = 2}
      {f = λ Y → if same (x [ t ≔ Y zero ]) z
                 then zpow (Along.E₁₅ c₁≢c₂ c₁≢t c₂≢t x Y) else 0ᴬ}
      {g = pathsum c₁ c₂ t x z}
      (λ Y → if-cong {p = same (x [ t ≔ Y zero ]) z} refl
                     (Along.phase-zpow c₁≢c₂ c₁≢t c₂≢t x Y))


------------------------------------------------------------------------
-- The theorem

-- The circuit computes the Toffoli function: its unnormalised amplitude
-- from x to z is √2² = 2 when z = x[t ≔ x_t ⊕ x_c₁ x_c₂], and 0
-- otherwise.

tof-computes : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
               (c₂≢t : c₂ ≢ t) →
               ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ computes toffoli c₁ c₂ t
tof-computes c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t = computing λ x z →
  tof-amp c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x z
  ∙ Σ-pathsum c₁ c₂ t x z
  ∙ scale-two (δ (toffoli c₁ c₂ t x) z)
  ∙ scale-exp {2} {norm (tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t)}
              (δ (toffoli c₁ c₂ t x) z) refl

-- So its path-sum is the classical path-sum of the Toffoli gate.

tof-spec : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
           (c₂≢t : c₂ ≢ t) →
           ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ ≋ toffoliˢ c₁ c₂ t
tof-spec c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t =
  computes⇒≋classical ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧
    (setWire t (liftᵉ (toffoliᵉ c₁ c₂ t)))
    (computes-≗ ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧
      (λ x w → sym (fun-toffoliˢ c₁ c₂ t x w))
      (tof-computes c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t))


------------------------------------------------------------------------
-- Two Toffoli gates cancel

-- The Toffoli function is an involution, so the circuit followed by
-- itself computes the identity (PathSum.Classical.⟦++⟧-computes, which
-- is PathSum.Compose.CRK's ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧ read on columns): its
-- unnormalised amplitude from x to z is √2⁴ δ x z.  By
-- PathSum.Classical.computes⇒≋classical that says ⟦ tof ++ tof ⟧ ≋
-- classical idᶜ, but that consequence is not drawn here: for this
-- circuit, 30 gates on arbitrary wires, Agda matched the lemma's
-- conclusion against the stated ≋ only by unfolding both into
-- amplitudes, and exhausted the 6 GB allowed -- even through a lemma
-- about a variable circuit, instantiated -- whereas the ≋ statement on
-- its own, and the computes form below, check in seconds.  Composites
-- of concrete circuits are therefore best stated with _computes_ (a
-- record, compared by its arguments).

tof-tof : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
          (c₂≢t : c₂ ≢ t) →
          ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ++ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧
            computes (λ x → x)
tof-tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t =
  computes-≗ ⟦ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t
               ++ tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧
    (toffoli-involutive c₁ c₂ t c₁≢t c₂≢t)
    (⟦++⟧-computes (tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t)
                   (tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t)
                   (tof-computes c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t)
                   (tof-computes c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t))

