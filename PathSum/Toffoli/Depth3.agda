------------------------------------------------------------------------
-- Presentations of groups
--
-- The Toffoli circuit of the paper's tool, on any three wires (Amy,
-- QPL 2018, section 5.2 and table 2)
--
-- The paper's tool, Feynman (github.com/meamy/feynman), expands every
-- Toffoli gate of its reversible benchmarks into Clifford+T by its
-- function toffoli (src/Feynman/Verification/SOP.hs):
--
--    toffoli x y z = H z; T x; T y; T z; CNOT x y; CNOT y z; CNOT z x;
--                    T† x; T† y; T z; CNOT y x; T† x;
--                    CNOT y z; CNOT z x; CNOT x y; H z
--
-- -- seven T gates in three layers (T-depth 3), seven CNOTs and two
-- Hadamards: sixteen gates, nine of them Clifford.  PathSum.Toffoli's
-- tof, Nielsen and Chuang's figure 4.9 with the T† and S on the second
-- control merged into one T, has six CNOTs and eight Clifford gates;
-- the figure itself has nine too (six CNOTs, two Hadamards, an S), so
-- table 2's nine per Toffoli gate fits either, and the tool's source
-- settles that it is this circuit's.  Here it is as tof₃ c₁ c₂ t, over
-- {H, CNOT, T, T†} (T = R_3), with controls c₁, c₂ (the tool's x, y)
-- and target t (its z) any three distinct wires, and the theorem that
-- it computes the Toffoli function (tof₃-computes), i.e. that its
-- path-sum is ≋ the classical path-sum toffoliˢ (tof₃-spec).
--
-- The proof is PathSum.Toffoli's, read along the paths of this
-- circuit.  Its Hadamards allocate y₁ (the first) and y₂ (the second,
-- the head variable); along a path the wires read x except that
-- between the Hadamards c₁, c₂ and t take the values of the CNOT
-- network -- c₂: x₂ ⊕ x₁, t: y₁ ⊕ x₂ ⊕ x₁, c₁: x₁ ⊕ t, then ⊕ c₂, then
-- ⊕ t again, and so on (Along.simulation, through
-- PathSum.Toffoli.Gate's three-wire assignments w3, with two lemmas
-- added here for CNOTs onto c₁) -- and at the end c₁ and c₂ read x₁
-- and x₂ again, and t reads y₂.  The phase is ½ x_t y₁ + ½ y₁ y₂ plus,
-- from the seven T and T†, 2^(M-3) times
--
--    x₁ + x₂ + y₁ − (y₁ ⊕ x₂) − (x₂ ⊕ x₁) + (y₁ ⊕ x₂ ⊕ x₁) − (y₁ ⊕ x₁)
--       = 4 x₁ x₂ y₁
--
-- (bracket₃, by cases; the wire values appear as the circuit computes
-- them), which is ½ x₁ x₂ y₁.  So along every path the outputs are
-- x[t ≔ y₂] and the phase is example 3.3's
-- ½ (x_t y₁ + x_c₁ x_c₂ y₁ + y₁ y₂) -- exactly tof's -- and the sum
-- over the paths is PathSum.Toffoli's (PathSum.Toffoli.Gate.
-- Σ-pathsum).  No polynomial is computed, and the circuit is never
-- evaluated as a closed instance.
--
-- Resources (tof₃-tcount, tof₃-cliffords, tof₃-norm): seven T or T†
-- gates, nine Clifford gates, two path variables.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Toffoli.Depth3 (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-assoc; +-comm; *-zeroʳ; *-distribˡ-+;
   neg-distribʳ-*)
open import Data.List.Base using ([]; _∷_; length)
open import Data.Nat.Base using (_∸_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (scale-exp)
open import PathSum.Assign using ([_]ᶻ; _[_≔_]; same; ≔-≔; ≔-comm; ≔-cong)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; computing; computes-≗; computes⇒≋classical; setWire)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.CRK.Path M₀ using
  (H; CNOT; R; R†; Circuit; ⟦_⟧; norm; init; Sim; end; R-sim; R†-sim;
   CNOT-sim; H-sim; sim-outBit; sim-phase; amp-sim)
open import PathSum.Cyclotomic M₀ using (Amp; 0ᴬ; _≐_; Σᴮ; Σᴮ-cong; zpow)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Boolean using (liftᵉ)
open import PathSum.QFT.Count M₀ using (cliffords)
open import PathSum.Reduction M using (½)
open import PathSum.Toffoli.Arith M₀ using
  (four-T; swap-last; zpow-½³; phase-bit; scale-two)
open import PathSum.Toffoli.Gate M₀ using
  (toffoli; toffoliᵉ; toffoliˢ; fun-toffoliˢ; pathsum; Σ-pathsum;
   module Wires)
open import PathSum.Toffoli.Netlist M₀ using (tcount)
open import PathSum.Base using (phase)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)


------------------------------------------------------------------------
-- The circuit

-- The tool's toffoli x y z with x, y, z = c₁, c₂, t.  The head of the
-- list is applied first.

tof₃ : (c₁ c₂ t : Fin n) → c₁ ≢ c₂ → c₁ ≢ t → c₂ ≢ t → Circuit n
tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t =
  H t ∷ R 3 c₁ ∷ R 3 c₂ ∷ R 3 t ∷
  CNOT c₁ c₂ c₁≢c₂ ∷ CNOT c₂ t c₂≢t ∷ CNOT t c₁ (λ e → c₁≢t (sym e)) ∷
  R† 3 c₁ ∷ R† 3 c₂ ∷ R 3 t ∷
  CNOT c₂ c₁ (λ e → c₁≢c₂ (sym e)) ∷ R† 3 c₁ ∷
  CNOT c₂ t c₂≢t ∷ CNOT t c₁ (λ e → c₁≢t (sym e)) ∷ CNOT c₁ c₂ c₁≢c₂ ∷
  H t ∷ []

-- Seven T or T†, nine Clifford gates (two Hadamards, seven CNOTs), two
-- path variables, sixteen gates.

tof₃-tcount : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
              (c₂≢t : c₂ ≢ t) → tcount (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) ≡ 7
tof₃-tcount c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t = refl

tof₃-cliffords : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
                 (c₂≢t : c₂ ≢ t) →
                 cliffords (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) ≡ 9
tof₃-cliffords c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t = refl

tof₃-norm : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
            (c₂≢t : c₂ ≢ t) → norm (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) ≡ 2
tof₃-norm c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t = refl

tof₃-length : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
              (c₂≢t : c₂ ≢ t) → length (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) ≡ 16
tof₃-length c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t = refl


------------------------------------------------------------------------
-- The arithmetic of a path

-- The values the CNOT network gives the wires, as the circuit computes
-- them (b for y₁): c₂ reads β₁ = x₂ ⊕ x₁; t reads γ₁ = y₁ ⊕ β₁, then
-- γ₂ = γ₁ ⊕ β₁; c₁ reads α₁ = x₁ ⊕ γ₁, α₂ = α₁ ⊕ β₁, α₃ = α₂ ⊕ γ₂;
-- and c₂ at the end β₂ = β₁ ⊕ α₃.

private
  β₁ᶠ : Bool → Bool → Bool
  β₁ᶠ x₁ x₂ = x₂ xor x₁

  γ₁ᶠ α₁ᶠ α₂ᶠ γ₂ᶠ α₃ᶠ β₂ᶠ : Bool → Bool → Bool → Bool
  γ₁ᶠ b x₁ x₂ = b xor β₁ᶠ x₁ x₂
  α₁ᶠ b x₁ x₂ = x₁ xor γ₁ᶠ b x₁ x₂
  α₂ᶠ b x₁ x₂ = α₁ᶠ b x₁ x₂ xor β₁ᶠ x₁ x₂
  γ₂ᶠ b x₁ x₂ = γ₁ᶠ b x₁ x₂ xor β₁ᶠ x₁ x₂
  α₃ᶠ b x₁ x₂ = α₂ᶠ b x₁ x₂ xor γ₂ᶠ b x₁ x₂
  β₂ᶠ b x₁ x₂ = β₁ᶠ x₁ x₂ xor α₃ᶠ b x₁ x₂

  -- At the end t reads y₁ again before the second Hadamard, and c₁, c₂
  -- read x₁, x₂.

  γ₂-back : ∀ b x₁ x₂ → γ₂ᶠ b x₁ x₂ ≡ b
  γ₂-back false false false = refl
  γ₂-back false false true  = refl
  γ₂-back false true  false = refl
  γ₂-back false true  true  = refl
  γ₂-back true  false false = refl
  γ₂-back true  false true  = refl
  γ₂-back true  true  false = refl
  γ₂-back true  true  true  = refl

  α₃-back : ∀ b x₁ x₂ → α₃ᶠ b x₁ x₂ ≡ x₁
  α₃-back false false false = refl
  α₃-back false false true  = refl
  α₃-back false true  false = refl
  α₃-back false true  true  = refl
  α₃-back true  false false = refl
  α₃-back true  false true  = refl
  α₃-back true  true  false = refl
  α₃-back true  true  true  = refl

  β₂-back : ∀ b x₁ x₂ → β₂ᶠ b x₁ x₂ ≡ x₂
  β₂-back false false false = refl
  β₂-back false false true  = refl
  β₂-back false true  false = refl
  β₂-back false true  true  = refl
  β₂-back true  false false = refl
  β₂-back true  false true  = refl
  β₂-back true  true  false = refl
  β₂-back true  true  true  = refl

  -- The seven T and T† add 2^(M-3) times this signed sum of bits,
  -- which is 4 x₁ x₂ y₁.

  bracket₃ : ∀ b x₁ x₂ →
    0ℤ + [ x₁ ]ᶻ + [ x₂ ]ᶻ + [ b ]ᶻ - [ α₁ᶠ b x₁ x₂ ]ᶻ - [ β₁ᶠ x₁ x₂ ]ᶻ
    + [ γ₁ᶠ b x₁ x₂ ]ᶻ - [ α₂ᶠ b x₁ x₂ ]ᶻ
    ≡ (+ 4) * [ (x₁ ∧ x₂) ∧ b ]ᶻ
  bracket₃ false false false = refl
  bracket₃ false false true  = refl
  bracket₃ false true  false = refl
  bracket₃ false true  true  = refl
  bracket₃ true  false false = refl
  bracket₃ true  false true  = refl
  bracket₃ true  true  false = refl
  bracket₃ true  true  true  = refl

  -- Collecting the multiples of T in a running sum B, one term at a
  -- time (as in PathSum.Toffoli.Arith).

  acc0 : ∀ a T → 0ℤ + a ≡ a + T * 0ℤ
  acc0 a T = trans (+-identityˡ a)
    (sym (trans (cong (λ w → a + w) (*-zeroʳ T)) (+-identityʳ a)))

  acc+ : ∀ a T B v {u} → u ≡ a + T * B → u + T * v ≡ a + T * (B + v)
  acc+ a T B v eq = trans (cong (_+ T * v) eq)
    (trans (+-assoc a (T * B) (T * v))
           (cong (λ w → a + w) (sym (*-distribˡ-+ T B v))))

  acc- : ∀ a T B v {u} → u ≡ a + T * B → u - T * v ≡ a + T * (B - v)
  acc- a T B v eq = trans (cong (_- T * v) eq)
    (trans (+-assoc a (T * B) (- (T * v)))
      (cong (λ w → a + w)
            (trans (cong (λ w → T * B + w) (neg-distribʳ-* T v))
                   (sym (*-distribˡ-+ T B (- v))))))

  accH : ∀ a T B q {u} → u ≡ a + T * B → u + q ≡ a + q + T * B
  accH a T B q eq = trans (cong (_+ q) eq)
    (trans (+-assoc a (T * B) q)
      (trans (cong (λ w → a + w) (+-comm (T * B) q))
             (sym (+-assoc a q (T * B)))))

  -- The phase along a path, tidied: the two Hadamards' terms, and T
  -- times the signed sum above.

  tidy₃ : ∀ h T p q f₁ f₂ f₃ e₁ e₂ e₃ e₄ →
    0ℤ + h * p + T * f₁ + T * f₂ + T * f₃ - T * e₁ - T * e₂ + T * e₃
    - T * e₄ + h * q
    ≡ h * p + h * q + T * (0ℤ + f₁ + f₂ + f₃ - e₁ - e₂ + e₃ - e₄)
  tidy₃ h T p q f₁ f₂ f₃ e₁ e₂ e₃ e₄ =
    accH a T B₇ (h * q) (acc- a T B₆ e₄ (acc+ a T B₅ e₃ (acc- a T B₄ e₂
      (acc- a T B₃ e₁ (acc+ a T B₂ f₃ (acc+ a T B₁ f₂
        (acc+ a T 0ℤ f₁ (acc0 a T))))))))
    where
    a B₁ B₂ B₃ B₄ B₅ B₆ B₇ : ℤ
    a  = h * p
    B₁ = 0ℤ + f₁
    B₂ = B₁ + f₂
    B₃ = B₂ + f₃
    B₄ = B₃ - e₁
    B₅ = B₄ - e₂
    B₆ = B₅ + e₃
    B₇ = B₆ - e₄


------------------------------------------------------------------------
-- The circuit along one path

-- Along the path Y, at the input x.  Y zero is y₂, the second
-- Hadamard's variable, and Y (suc zero) is y₁, the first's.

module Along {n : ℕ} {c₁ c₂ t : Fin n} (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
             (c₂≢t : c₂ ≢ t) (x : Assign n) (Y : Assign 2) where

  open Wires c₁≢c₂ c₁≢t c₂≢t x

  -- The CNOTs onto c₁ (the circuit here has four; tof has none).

  w3-set-c₁ : ∀ α β γ α′ u → (w3 α β γ [ c₁ ≔ α′ ]) u ≡ w3 α′ β γ u
  w3-set-c₁ α β γ α′ u =
    trans (≔-comm (x [ c₁ ≔ α ] [ c₂ ≔ β ]) γ α′ (λ e → c₁≢t (sym e)) u)
          (≔-cong t γ (λ v →
             trans (≔-comm (x [ c₁ ≔ α ]) β α′ (λ e → c₁≢c₂ (sym e)) v)
                   (≔-cong c₂ β (≔-≔ x c₁ α α′) v)) u)

  cnot-c₁ : (c : Fin n) (α β γ v : Bool) → w3 α β γ c ≡ v →
            ∀ u → (w3 α β γ [ c₁ ≔ w3 α β γ c₁ xor w3 α β γ c ]) u ≡
                  w3 (α xor v) β γ u
  cnot-c₁ c α β γ v eq u =
    trans (cong (λ b → (w3 α β γ [ c₁ ≔ b ]) u)
                (cong₂ _xor_ (w3-c₁ α β γ) eq))
          (w3-set-c₁ α β γ (α xor v) u)

  private
    x₁ x₂ xₜ y₁ y₂ : Bool
    x₁ = x c₁
    x₂ = x c₂
    xₜ = x t
    y₁ = Y (suc zero)
    y₂ = Y zero

    β₁ γ₁ α₁ α₂ γ₂ α₃ β₂ : Bool
    β₁ = β₁ᶠ x₁ x₂
    γ₁ = γ₁ᶠ y₁ x₁ x₂
    α₁ = α₁ᶠ y₁ x₁ x₂
    α₂ = α₂ᶠ y₁ x₁ x₂
    γ₂ = γ₂ᶠ y₁ x₁ x₂
    α₃ = α₃ᶠ y₁ x₁ x₂
    β₂ = β₂ᶠ y₁ x₁ x₂

    T : ℤ
    T = pow (M ∸ 3)

  -- The phase value after the first Hadamard (E₁), after each phase
  -- gate, and after the second Hadamard (E₁₆).

  E₁ E₂ E₃ E₄ E₈ E₉ E₁₀ E₁₂ E₁₆ : ℤ
  E₁  = 0ℤ + ½ * [ xₜ ∧ y₁ ]ᶻ
  E₂  = E₁ + T * [ x₁ ]ᶻ
  E₃  = E₂ + T * [ x₂ ]ᶻ
  E₄  = E₃ + T * [ y₁ ]ᶻ
  E₈  = E₄ - T * [ α₁ ]ᶻ
  E₉  = E₈ - T * [ β₁ ]ᶻ
  E₁₀ = E₉ + T * [ γ₁ ]ᶻ
  E₁₂ = E₁₀ - T * [ α₂ ]ᶻ
  E₁₆ = E₁₂ + ½ * [ γ₂ ∧ y₂ ]ᶻ

  -- The simulation, gate by gate.  At the end the wires read x, except
  -- t, which reads y₂.

  simulation : Sim x (x [ t ≔ Y zero ]) E₁₆ (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t)
                   init Y x 0ℤ
  simulation =
    H-sim {e₁ = E₁} refl (w3-x y₁) refl
    (R-sim {e₁ = E₂} (w3-c₁ x₁ x₂ y₁) refl
    (R-sim {e₁ = E₃} (w3-c₂ x₁ x₂ y₁) refl
    (R-sim {e₁ = E₄} (w3-t x₁ x₂ y₁) refl
    (CNOT-sim (cnot-c₂ x₁ x₂ y₁)
    (CNOT-sim (cnot-t c₂ x₁ β₁ y₁ β₁ (w3-c₂ x₁ β₁ y₁))
    (CNOT-sim (cnot-c₁ t x₁ β₁ γ₁ γ₁ (w3-t x₁ β₁ γ₁))
    (R†-sim {e₁ = E₈} (w3-c₁ α₁ β₁ γ₁) refl
    (R†-sim {e₁ = E₉} (w3-c₂ α₁ β₁ γ₁) refl
    (R-sim {e₁ = E₁₀} (w3-t α₁ β₁ γ₁) refl
    (CNOT-sim (cnot-c₁ c₂ α₁ β₁ γ₁ β₁ (w3-c₂ α₁ β₁ γ₁))
    (R†-sim {e₁ = E₁₂} (w3-c₁ α₂ β₁ γ₁) refl
    (CNOT-sim (cnot-t c₂ α₂ β₁ γ₁ β₁ (w3-c₂ α₂ β₁ γ₁))
    (CNOT-sim (cnot-c₁ t α₂ β₁ γ₂ γ₂ (w3-t α₂ β₁ γ₂))
    (CNOT-sim (cnot-c₂ α₃ β₁ γ₂)
    (H-sim {e₁ = E₁₆} (w3-t α₃ β₂ γ₂) (h-t α₃ β₂ γ₂ y₂ refl) refl
    (end (λ u → trans (cong₂ (λ α β → w3 α β y₂ u)
                             (α₃-back y₁ x₁ x₂) (β₂-back y₁ x₁ x₂))
                      (sym (w3-x y₂ u)))
         refl))))))))))))))))

  -- The phase: ½ x_t y₁ + ½ x₁ x₂ y₁ + ½ y₁ y₂, exactly.

  exact : E₁₆ ≡ ½ * [ x t ∧ Y (suc zero) ]ᶻ
                + ½ * [ (x c₁ ∧ x c₂) ∧ Y (suc zero) ]ᶻ
                + ½ * [ Y (suc zero) ∧ Y zero ]ᶻ
  exact =
    trans (tidy₃ ½ T [ xₜ ∧ y₁ ]ᶻ [ γ₂ ∧ y₂ ]ᶻ [ x₁ ]ᶻ [ x₂ ]ᶻ [ y₁ ]ᶻ
                 [ α₁ ]ᶻ [ β₁ ]ᶻ [ γ₁ ]ᶻ [ α₂ ]ᶻ)
    (trans (cong₂ (λ q s → ½ * [ xₜ ∧ y₁ ]ᶻ + q + s)
                  (cong (λ v → ½ * [ v ∧ y₂ ]ᶻ) (γ₂-back y₁ x₁ x₂))
                  (trans (cong (T *_) (bracket₃ y₁ x₁ x₂))
                         (four-T [ (x₁ ∧ x₂) ∧ y₁ ]ᶻ)))
           (swap-last (½ * [ xₜ ∧ y₁ ]ᶻ) (½ * [ y₁ ∧ y₂ ]ᶻ)
                      (½ * [ (x₁ ∧ x₂) ∧ y₁ ]ᶻ)))

  -- Modulo 1: ½ · (y₁ ∧ (y₂ ⊕ x_t ⊕ x₁ x₂)).

  phase-zpow : zpow E₁₆ ≐
               zpow (½ * [ Y (suc zero) ∧
                           (Y zero xor (x t xor (x c₁ ∧ x c₂))) ]ᶻ)
  phase-zpow = zpow-≡ exact
    ∙ zpow-½³ (x t ∧ Y (suc zero)) ((x c₁ ∧ x c₂) ∧ Y (suc zero))
              (Y (suc zero) ∧ Y zero)
    ∙ zpow-≡ (cong (λ d → ½ * [ d ]ᶻ)
                   (phase-bit (x t) (x c₁ ∧ x c₂) (Y zero) (Y (suc zero))))


------------------------------------------------------------------------
-- The circuit's path-sum, path by path

-- Along the path Y the outputs are x[t ≔ y₂] and the phase is
-- ½ x_t y₁ + ½ x_c₁ x_c₂ y₁ + ½ y₁ y₂: the path-sum of PathSum.Toffoli's
-- circuit, and example 3.3's.

tof₃-outputs : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
               (c₂≢t : c₂ ≢ t) (x : Assign n) (Y : Assign 2) →
               ∀ u → outBit ⟦ tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ x Y u ≡
                     (x [ t ≔ Y zero ]) u
tof₃-outputs c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x Y =
  sim-outBit (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) x Y
             (Along.simulation c₁≢c₂ c₁≢t c₂≢t x Y)

tof₃-phase : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
             (c₂≢t : c₂ ≢ t) (x : Assign n) (Y : Assign 2) →
             eval (phase ⟦ tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧) x Y ≡
             ½ * [ x t ∧ Y (suc zero) ]ᶻ
             + ½ * [ (x c₁ ∧ x c₂) ∧ Y (suc zero) ]ᶻ
             + ½ * [ Y (suc zero) ∧ Y zero ]ᶻ
tof₃-phase c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x Y =
  trans (sim-phase (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) x Y
                   (Along.simulation c₁≢c₂ c₁≢t c₂≢t x Y))
        (Along.exact c₁≢c₂ c₁≢t c₂≢t x Y)

-- Its amplitude from x to z: over the four paths, ζ^(½ y₁ q) at the
-- paths whose output x[t ≔ y₂] is z, q being y₂ ⊕ x_t ⊕ x_c₁ x_c₂.

tof₃-amp : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
           (c₂≢t : c₂ ≢ t) (x z : Assign n) →
           amp ⟦ tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ x z ≐
           Σᴮ (pathsum c₁ c₂ t x z)
tof₃-amp c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x z =
  amp-sim (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t) x z (λ Y → x [ t ≔ Y zero ])
          (Along.E₁₆ c₁≢c₂ c₁≢t c₂≢t x)
          (Along.simulation c₁≢c₂ c₁≢t c₂≢t x)
  ∙ Σᴮ-cong {k = 2}
      {f = λ Y → if same (x [ t ≔ Y zero ]) z
                 then zpow (Along.E₁₆ c₁≢c₂ c₁≢t c₂≢t x Y) else 0ᴬ}
      {g = pathsum c₁ c₂ t x z}
      (λ Y → if-cong {p = same (x [ t ≔ Y zero ]) z} refl
                     (Along.phase-zpow c₁≢c₂ c₁≢t c₂≢t x Y))


------------------------------------------------------------------------
-- The theorem

-- The circuit computes the Toffoli function: its unnormalised amplitude
-- from x to z is √2² = 2 when z = x[t ≔ x_t ⊕ x_c₁ x_c₂], and 0
-- otherwise.

tof₃-computes : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
                (c₂≢t : c₂ ≢ t) →
                ⟦ tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ computes toffoli c₁ c₂ t
tof₃-computes c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t = computing λ x z →
  tof₃-amp c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t x z
  ∙ Σ-pathsum c₁ c₂ t x z
  ∙ scale-two (δ (toffoli c₁ c₂ t x) z)
  ∙ scale-exp {2} {norm (tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t)}
              (δ (toffoli c₁ c₂ t x) z) refl

-- So its path-sum is the classical path-sum of the Toffoli gate.

tof₃-spec : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
            (c₂≢t : c₂ ≢ t) →
            ⟦ tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ ≋ toffoliˢ c₁ c₂ t
tof₃-spec c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t =
  computes⇒≋classical ⟦ tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧
    (setWire t (liftᵉ (toffoliᵉ c₁ c₂ t)))
    (computes-≗ ⟦ tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧
      (λ x w → sym (fun-toffoliˢ c₁ c₂ t x w))
      (tof₃-computes c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t))
