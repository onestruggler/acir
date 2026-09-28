------------------------------------------------------------------------
-- Presentations of groups
--
-- The relative-phase Toffoli-4 gate on any four wires (Amy, QPL 2018,
-- section 5.2; Maslov, Phys. Rev. A 93, 2016, the paper's [23])
--
-- A relative-phase Toffoli gate with three controls a, b, c and target
-- d, over {H, CNOT, T, T†}: eight T gates, four Hadamards and six
-- CNOTs, the target sandwiched thus
--
--    rc3x a b c d = H T CNOT(c,d) T† H ;
--                   CNOT(a,d) T CNOT(b,d) T† CNOT(a,d) T CNOT(b,d) T† ;
--                   H T CNOT(c,d) T† H                  (all on d)
--
-- on any wires with a, b, c ≠ d, for every n and every M = 3 + M₀.  It
-- is figure 4 of [23] gate for gate (Maslov, arXiv:1508.03273, whose
-- printed matrix is the relative phase below), the relative-phase
-- three-control Toffoli gate circuit libraries ship, and the paper's
-- tool's rToffoli4 (Feynman's src/Feynman/Verification/SOP.hs), of
-- which its Maslov benchmark is built.  PathSum.RelativePhase's header
-- explains why it is the
-- gate the decomposition of section 5.2 is made of: table 2's counts
-- for Maslov50 and Maslov100 are those of n - 2 of these gates and one
-- CNOT, on n + ⌈(n-3)/2⌉ wires (the paper's count of ancillas).
--
-- The theorem (rc3x-up-to) is that it computes the three-control
-- Toffoli function up to a relative phase, computed exactly:
--
--    |x⟩ ↦ i^(x_a x_b) i^(x_a x_b x_c) (-1)^(x_a x_b x_d)
--            |x[d ≔ x_d ⊕ x_a x_b x_c]⟩,
--
-- the phase ¼ x_a x_b + ¼ x_a x_b x_c + ½ x_a x_b x_d (rc3x-phase) read
-- before the gate; so its path-sum is ≋ the path-sum without path
-- variables with that phase polynomial and that output on d
-- (rc3x-spec), and it does not compute the Toffoli-4 function exactly
-- (rc3x-not-toffoli), which a path-sum ≋ the Toffoli-4 gate's would
-- (≋toffoli₄⇒computes).
--
-- Unlike PathSum.Maslov.Gate, this module exports no statement about
-- the gate's amplitudes path by path (the amplitude as a sum over the
-- paths, rc3x-amp, is private): restated in another module, a
-- statement about amp, outBit or eval at this four-Hadamard circuit is
-- compared by running the circuit, at about a minute and a half per
-- statement.  What is exported is stated through the records
-- _computes_up-to_ and _computes_, which compare cheaply; rc3x-spec,
-- stated with ≋, is the exception (and costs as much to restate).
--
-- The route is the gate's amplitudes, path by path, as for
-- PathSum.Maslov.Gate, but the sum over the paths is not done by
-- Boolean identities.  Along a path y₁ … y₄ (y₄ the last Hadamard's
-- variable, the head) the target reads y₁, y₁ ⊕ x_c, y₂, y₂ ⊕ x_a, … ,
-- y₃ ⊕ x_c and finally y₄, and the phase is ⅛ times an integer computed
-- from x_a, x_b, x_c, x_d and the yᵢ (phase⁸; the simulation keeps the
-- phase in that form, gate by gate).  Its terms in y₁ and y₃ include
-- ¼ x_c y₁ and ¼ x_c y₃, so when x_c = 1 the sums over y₁ and y₃ are
-- 1 ± i rather than 2 or 0, and the four-variable sum cancels only as
-- a whole.  It is evaluated by PathSum.Maslov.Eighths: for each value
-- of x_a, x_b, x_c, x_d and y₄ Agda computes the sum over y₁, y₂, y₃ as
-- an integer combination of the eighth roots of unity and compares it,
-- by refl, with 4 ζ^(relative phase) at the Toffoli function's value
-- of y₄ and with 0 at the other (eval⁸, 32 cases).
--
-- Undoing the gate.  Unlike the three-qubit gate this circuit is not
-- its own inverse: its inverse (PathSum.CRK.Adjoint's _†) computes the
-- same permutation up to minus the phase read after it (rc3x†-up-to,
-- by PathSum.RelativePhase.†-up-to), so the gate followed by its
-- inverse computes the identity exactly (rc3x-rc3x†), and around any
-- circuit that leaves a, b, c and d alone the gate and its inverse
-- cancel their phases (rc3x-sandwich).  It has to be the inverse:
-- followed by itself, as an involution would be, the gate leaves the
-- phase φ(x) + φ(T x) behind, -1 at x_a = x_b = x_c = 1, x_d = 0, and
-- the pair is not the identity (rc3x-rc3x-not-id).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Maslov.Gate4 (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-inverseʳ; *-identityˡ; *-identityʳ; *-zeroʳ;
   *-distribˡ-+; neg-distribʳ-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (_∸_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (scale-+; scale-twice)
open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-self; ≔-cong; same)
open import PathSum.Base using (PathSum)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; computes-≗; ≋classical⇒computes; none; classical;
   setWire; fun-setWireᵉ)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡; rot-if; if-Σᴮ)
open import PathSum.CRK.Adjoint M using (_†)
open import PathSum.CRK.Path M₀ using
  (H; CNOT; R; R†; Circuit; ⟦_⟧; norm; paths; init; Sim; end; R-sim;
   R†-sim; CNOT-sim; H-sim; amp-sim)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _·ᴬ_; _≐_; extend; Σᴮ; zpow; zpow-anti; zpow0-at-0; 0ᶠ;
   rot; scale; N)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.Maslov.Arith M₀ using (two-⅛; ¼+¼; ½+½)
open import PathSum.Maslov.Eighths M₀ using
  (Lin; ⟦_⟧ˡ; 0ˡ; _·ˡ_; ⟦·ˡ⟧; unitˡ; unit-ok; Σˡ; Σˡ-cong; Respectsᴮ;
   extend-≗; Σᴮ-ˡ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Poly; x[_]; eval; _+ᴾ_; _·ᴾ_)
open import PathSum.Polynomial.Boolean using
  (BExp; ⟦_⟧ᵉ; var; _⊕ᵉ_; _∧ᵉ_; liftᵉ; eval-liftᵉ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-·ᴾ)
open import PathSum.Reduction M using (⅛; ¼; ½)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-≡; ≡ᴺ-refl; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ-N; zpow-≡ᴺ; _computes_up-to_;
   computing-up-to; up-to-≗; up-to-phase; up-to⇒computes; up-to-exact;
   phased; up-to⇒≋phased; ⟦++⟧-up-to; sandwich; Respects-φ; Respects-F;
   †-up-to)
open import PathSum.Toffoli.Arith M₀ using (four-T; select)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  -- PathSum.CRK.Path.amp-sim, restated for any circuit.  Applied
  -- directly at this circuit, amp-sim's instance did not match this
  -- module's statement of it syntactically, and Agda compared the two
  -- by unfolding amp at the circuit -- by running the circuit -- which
  -- cost about eighty seconds; the restatement's instance matches, and
  -- the restatement itself is checked at a variable circuit, where
  -- nothing unfolds.  (For the same reason the proofs below never write
  -- the path-sum ⟦ rc3x … ⟧ out as an argument, which cost as much
  -- again each time, but leave it to be inferred from the statement.)

  amp-sim′ : (C : Circuit n) (x z : Assign n)
             (a′ : Assign (paths C) → Assign n)
             (e′ : Assign (paths C) → ℤ) →
             (∀ y → Sim x (a′ y) (e′ y) C init y x 0ℤ) →
             amp ⟦ C ⟧ x z ≐
             Σᴮ (λ y → if same (a′ y) z then zpow (e′ y) else 0ᴬ)
  amp-sim′ C x z a′ e′ s = amp-sim C x z a′ e′ s


------------------------------------------------------------------------
-- The circuit and its specification

-- Controls a, b and c, target d (T = R 3, T† = R† 3).  The head of the
-- list is applied first.

rc3x : (a b c d : Fin n) → a ≢ d → b ≢ d → c ≢ d → Circuit n
rc3x a b c d a≢d b≢d c≢d =
  H d ∷ R 3 d ∷ CNOT c d c≢d ∷ R† 3 d ∷ H d ∷
  CNOT a d a≢d ∷ R 3 d ∷ CNOT b d b≢d ∷ R† 3 d ∷
  CNOT a d a≢d ∷ R 3 d ∷ CNOT b d b≢d ∷ R† 3 d ∷
  H d ∷ R 3 d ∷ CNOT c d c≢d ∷ R† 3 d ∷ H d ∷ []

-- The three-control Toffoli function, and the relative phase, a
-- numerator over 2^M: ¼ x_a x_b + ¼ x_a x_b x_c + ½ x_a x_b x_d.

toffoli₄ : (a b c d : Fin n) → Assign n → Assign n
toffoli₄ a b c d x = x [ d ≔ x d xor ((x a ∧ x b) ∧ x c) ]

rc3x-phase : (a b c d : Fin n) → Assign n → ℤ
rc3x-phase a b c d x =
  ¼ * [ x a ∧ x b ]ᶻ + ¼ * [ (x a ∧ x b) ∧ x c ]ᶻ
  + ½ * [ (x a ∧ x b) ∧ x d ]ᶻ

-- The same as a phase polynomial, and the specification.

toffoli₄ᵉ : (a b c d : Fin n) → BExp n 0
toffoli₄ᵉ a b c d = var x[ d ] ⊕ᵉ ((var x[ a ] ∧ᵉ var x[ b ]) ∧ᵉ var x[ c ])

rc3xᴾ : (a b c d : Fin n) → Poly n 0
rc3xᴾ a b c d =
  (¼ ·ᴾ liftᵉ (var x[ a ] ∧ᵉ var x[ b ]))
  +ᴾ (¼ ·ᴾ liftᵉ ((var x[ a ] ∧ᵉ var x[ b ]) ∧ᵉ var x[ c ]))
  +ᴾ (½ ·ᴾ liftᵉ ((var x[ a ] ∧ᵉ var x[ b ]) ∧ᵉ var x[ d ]))

eval-rc3xᴾ : (a b c d : Fin n) (x : Assign n) →
             eval (rc3xᴾ a b c d) x none ≡ rc3x-phase a b c d x
eval-rc3xᴾ a b c d x = trans
  (eval-+ᴾ (A +ᴾ B) C x none)
  (cong₂ _+_ (trans (eval-+ᴾ A B x none) (cong₂ _+_ (term ¼ eA) (term ¼ eB)))
             (term ½ eC))
  where
  eA eB eC : BExp _ 0
  eA = var x[ a ] ∧ᵉ var x[ b ]
  eB = (var x[ a ] ∧ᵉ var x[ b ]) ∧ᵉ var x[ c ]
  eC = (var x[ a ] ∧ᵉ var x[ b ]) ∧ᵉ var x[ d ]

  A B C : Poly _ 0
  A = ¼ ·ᴾ liftᵉ eA
  B = ¼ ·ᴾ liftᵉ eB
  C = ½ ·ᴾ liftᵉ eC

  term : ∀ h e → eval (h ·ᴾ liftᵉ e) x none ≡ h * [ ⟦ e ⟧ᵉ x none ]ᶻ
  term h e = trans (eval-·ᴾ h (liftᵉ e) x none)
                   (cong (h *_) (eval-liftᵉ e x none))

toffoli₄ˢ : (a b c d : Fin n) → PathSum n 0 0
toffoli₄ˢ a b c d = classical (setWire d (liftᵉ (toffoli₄ᵉ a b c d)))

rc3xˢ : (a b c d : Fin n) → PathSum n 0 0
rc3xˢ a b c d = phased (rc3xᴾ a b c d) (setWire d (liftᵉ (toffoli₄ᵉ a b c d)))

-- The phase reads only a, b, c and d.

phase-at₄ : (a b c d : Fin n) (y : Assign n) {p q r s : Bool} →
            y a ≡ p → y b ≡ q → y c ≡ r → y d ≡ s →
            rc3x-phase a b c d y ≡
            ¼ * [ p ∧ q ]ᶻ + ¼ * [ (p ∧ q) ∧ r ]ᶻ + ½ * [ (p ∧ q) ∧ s ]ᶻ
phase-at₄ a b c d y refl refl refl refl = refl


------------------------------------------------------------------------
-- Phases in eighths

-- The relative phase is ⅛ Φ⁸, Φ⁸ = 2 x_a x_b + 2 x_a x_b x_c
-- + 4 x_a x_b x_d.

Φ⁸ : Bool → Bool → Bool → Bool → ℤ
Φ⁸ a b c d = (+ 2) * [ a ∧ b ]ᶻ + (+ 2) * [ (a ∧ b) ∧ c ]ᶻ
             + (+ 4) * [ (a ∧ b) ∧ d ]ᶻ

Φ⁸-ok : ∀ a b c d → ⅛ * Φ⁸ a b c d ≡
        ¼ * [ a ∧ b ]ᶻ + ¼ * [ (a ∧ b) ∧ c ]ᶻ + ½ * [ (a ∧ b) ∧ d ]ᶻ
Φ⁸-ok a b c d = trans
  (*-distribˡ-+ ⅛ ((+ 2) * [ a ∧ b ]ᶻ + (+ 2) * [ (a ∧ b) ∧ c ]ᶻ)
                  ((+ 4) * [ (a ∧ b) ∧ d ]ᶻ))
  (cong₂ _+_ (trans (*-distribˡ-+ ⅛ ((+ 2) * [ a ∧ b ]ᶻ)
                                   ((+ 2) * [ (a ∧ b) ∧ c ]ᶻ))
                    (cong₂ _+_ (two-⅛ [ a ∧ b ]ᶻ) (two-⅛ [ (a ∧ b) ∧ c ]ᶻ)))
             (four-T [ (a ∧ b) ∧ d ]ᶻ))

-- The phase along the path y₁ … y₄, in eighths: the first Hadamard's
-- ½ x_d y₁, the target's values under the T and T† gates, and the other
-- Hadamards' halves.

phase⁸ : (a b c d y₁ y₂ y₃ y₄ : Bool) → ℤ
phase⁸ a b c d y₁ y₂ y₃ y₄ =
  (+ 4) * [ d ∧ y₁ ]ᶻ + [ y₁ ]ᶻ - [ w₁ ]ᶻ + (+ 4) * [ w₁ ∧ y₂ ]ᶻ
  + [ w₂ ]ᶻ - [ w₃ ]ᶻ + [ w₄ ]ᶻ - [ w₅ ]ᶻ + (+ 4) * [ w₅ ∧ y₃ ]ᶻ
  + [ y₃ ]ᶻ - [ w₆ ]ᶻ + (+ 4) * [ w₆ ∧ y₄ ]ᶻ
  where
  w₁ w₂ w₃ w₄ w₅ w₆ : Bool
  w₁ = y₁ xor c
  w₂ = y₂ xor a
  w₃ = w₂ xor b
  w₄ = w₃ xor a
  w₅ = w₄ xor b
  w₆ = y₃ xor c

-- The same, read off the inputs and the whole path.  Opaque, so that
-- Agda compares two such phases under ζ by their arguments instead of
-- unfolding them (and ζ with them), which is costly.

opaque
  J⁸ : (a b c d : Fin n) → Assign n → Assign 4 → ℤ
  J⁸ a b c d x Y = phase⁸ (x a) (x b) (x c) (x d) (Y (suc (suc (suc zero))))
                          (Y (suc (suc zero))) (Y (suc zero)) (Y zero)

  J⁸-def : (a b c d : Fin n) (x : Assign n) (Y : Assign 4) →
           J⁸ a b c d x Y ≡
           phase⁸ (x a) (x b) (x c) (x d) (Y (suc (suc (suc zero))))
                  (Y (suc (suc zero))) (Y (suc zero)) (Y zero)
  J⁸-def a b c d x Y = refl

-- What a path contributes to the amplitude from x to z: its output is
-- x[d ≔ y₄], its phase ⅛ J⁸.

out⁴ : Fin n → Assign n → Assign 4 → Assign n
out⁴ d x Y = x [ d ≔ Y zero ]

ph⁴ : (a b c d : Fin n) → Assign n → Assign 4 → ℤ
ph⁴ a b c d x Y = ⅛ * J⁸ a b c d x Y

term⁴ : (a b c d : Fin n) → Assign n → Assign n → Assign 4 → Amp
term⁴ a b c d x z Y =
  if same (x [ d ≔ Y zero ]) z then zpow (⅛ * J⁸ a b c d x Y) else 0ᴬ

-- Adding a gate's contribution to a phase kept as ⅛ times an integer.

private
  acc-H₀ : ∀ q → 0ℤ + ½ * q ≡ ⅛ * ((+ 4) * q)
  acc-H₀ q = trans (+-identityˡ (½ * q)) (sym (four-T q))

  acc-R : ∀ J v → ⅛ * J + pow (M ∸ 3) * v ≡ ⅛ * (J + v)
  acc-R J v = sym (*-distribˡ-+ ⅛ J v)

  acc-R† : ∀ J v → ⅛ * J - pow (M ∸ 3) * v ≡ ⅛ * (J - v)
  acc-R† J v = sym (trans (*-distribˡ-+ ⅛ J (- v))
                          (cong (λ w → ⅛ * J + w) (sym (neg-distribʳ-* ⅛ v))))

  acc-H : ∀ J q → ⅛ * J + ½ * q ≡ ⅛ * (J + (+ 4) * q)
  acc-H J q = trans (cong (λ w → ⅛ * J + w) (sym (four-T q)))
                    (sym (*-distribˡ-+ ⅛ J ((+ 4) * q)))


------------------------------------------------------------------------
-- The circuit along one path

-- Along the path Y, at the input x: Y zero is y₄, the last Hadamard's
-- variable, and Y (suc (suc (suc zero))) is y₁, the first's.

private
  module Along {n : ℕ} {a b c d : Fin n} (a≢d : a ≢ d) (b≢d : b ≢ d)
               (c≢d : c ≢ d) (x : Assign n) (Y : Assign 4) where

    private
      xa xb xc xd y₁ y₂ y₃ y₄ : Bool
      xa = x a
      xb = x b
      xc = x c
      xd = x d
      y₁ = Y (suc (suc (suc zero)))
      y₂ = Y (suc (suc zero))
      y₃ = Y (suc zero)
      y₄ = Y zero

      -- What d reads after each CNOT.

      w₁ w₂ w₃ w₄ w₅ w₆ : Bool
      w₁ = y₁ xor xc
      w₂ = y₂ xor xa
      w₃ = w₂ xor xb
      w₄ = w₃ xor xa
      w₅ = w₄ xor xb
      w₆ = y₃ xor xc

      -- Only d is ever written: a CNOT onto d from a control adds its
      -- value.

      cnot : (e : Fin n) → e ≢ d → (γ : Bool) →
             ∀ u → ((x [ d ≔ γ ]) [ d ≔ (x [ d ≔ γ ]) d xor (x [ d ≔ γ ]) e ])
                     u ≡ (x [ d ≔ γ xor x e ]) u
      cnot e e≢d γ u =
        trans (cong (λ v → ((x [ d ≔ γ ]) [ d ≔ v ]) u)
                    (cong₂ _xor_ (≔-here x d γ) (≔-there x γ e≢d)))
              (≔-≔ x d γ (γ xor x e) u)

    -- The phase, ⅛ times these integers, after each gate that changes it.

    J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ : ℤ
    J₁  = (+ 4) * [ xd ∧ y₁ ]ᶻ
    J₂  = J₁ + [ y₁ ]ᶻ
    J₃  = J₂ - [ w₁ ]ᶻ
    J₄  = J₃ + (+ 4) * [ w₁ ∧ y₂ ]ᶻ
    J₅  = J₄ + [ w₂ ]ᶻ
    J₆  = J₅ - [ w₃ ]ᶻ
    J₇  = J₆ + [ w₄ ]ᶻ
    J₈  = J₇ - [ w₅ ]ᶻ
    J₉  = J₈ + (+ 4) * [ w₅ ∧ y₃ ]ᶻ
    J₁₀ = J₉ + [ y₃ ]ᶻ
    J₁₁ = J₁₀ - [ w₆ ]ᶻ
    J₁₂ = J₁₁ + (+ 4) * [ w₆ ∧ y₄ ]ᶻ

    -- The simulation: the wires read x except on d.

    simulation :
      Sim x (x [ d ≔ Y zero ]) (⅛ * J⁸ a b c d x Y)
          (rc3x a b c d a≢d b≢d c≢d) init Y x 0ℤ
    simulation =
      H-sim {e₁ = ⅛ * J₁} refl (λ _ → refl) (acc-H₀ [ xd ∧ y₁ ]ᶻ)
      (R-sim {e₁ = ⅛ * J₂} (≔-here x d y₁) (acc-R J₁ [ y₁ ]ᶻ)
      (CNOT-sim (cnot c c≢d y₁)
      (R†-sim {e₁ = ⅛ * J₃} (≔-here x d w₁) (acc-R† J₂ [ w₁ ]ᶻ)
      (H-sim {e₁ = ⅛ * J₄} (≔-here x d w₁) (λ u → ≔-≔ x d w₁ y₂ u)
             (acc-H J₃ [ w₁ ∧ y₂ ]ᶻ)
      (CNOT-sim (cnot a a≢d y₂)
      (R-sim {e₁ = ⅛ * J₅} (≔-here x d w₂) (acc-R J₄ [ w₂ ]ᶻ)
      (CNOT-sim (cnot b b≢d w₂)
      (R†-sim {e₁ = ⅛ * J₆} (≔-here x d w₃) (acc-R† J₅ [ w₃ ]ᶻ)
      (CNOT-sim (cnot a a≢d w₃)
      (R-sim {e₁ = ⅛ * J₇} (≔-here x d w₄) (acc-R J₆ [ w₄ ]ᶻ)
      (CNOT-sim (cnot b b≢d w₄)
      (R†-sim {e₁ = ⅛ * J₈} (≔-here x d w₅) (acc-R† J₇ [ w₅ ]ᶻ)
      (H-sim {e₁ = ⅛ * J₉} (≔-here x d w₅) (λ u → ≔-≔ x d w₅ y₃ u)
             (acc-H J₈ [ w₅ ∧ y₃ ]ᶻ)
      (R-sim {e₁ = ⅛ * J₁₀} (≔-here x d y₃) (acc-R J₉ [ y₃ ]ᶻ)
      (CNOT-sim (cnot c c≢d y₃)
      (R†-sim {e₁ = ⅛ * J₁₁} (≔-here x d w₆) (acc-R† J₁₀ [ w₆ ]ᶻ)
      (H-sim {e₁ = ⅛ * J₁₂} (≔-here x d w₆) (λ u → ≔-≔ x d w₆ (Y zero) u)
             (acc-H J₁₁ [ w₆ ∧ y₄ ]ᶻ)
      (end (λ _ → refl)
           (cong (⅛ *_) (sym (J⁸-def a b c d x Y)))))))))))))))))))))


------------------------------------------------------------------------
-- The gate's path-sum, path by path

-- Along the path Y the outputs are x[d ≔ y₄] and the phase is ⅛ J⁸
-- (the simulation above); so the amplitude from x to z is the sum,
-- over the sixteen paths, of ζ^(⅛ J⁸) at the paths whose output is z.
-- Kept private, as are the outputs and the phase along a path, which
-- PathSum.CRK.Path's sim-outBit and sim-phase read off the simulation
-- the same way: a statement about amp, outBit or eval at this circuit's
-- path-sum, restated in another module, is compared there by running
-- the circuit, at about a minute and a half per statement for this
-- four-Hadamard gate.  What other modules see is stated through the
-- records of PathSum.RelativePhase and PathSum.Classical, which compare
-- cheaply.

private
  rc3x-amp : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
             (c≢d : c ≢ d) (x z : Assign n) →
             amp ⟦ rc3x a b c d a≢d b≢d c≢d ⟧ x z ≐ Σᴮ (term⁴ a b c d x z)
  rc3x-amp a b c d a≢d b≢d c≢d x z =
    amp-sim′ (rc3x a b c d a≢d b≢d c≢d) x z (out⁴ d x) (ph⁴ a b c d x)
             (Along.simulation a≢d b≢d c≢d x)


------------------------------------------------------------------------
-- The sum over the paths, by computation

-- For given inputs and last variable β = y₄, the sum over y₁, y₂, y₃,
-- as a combination of eighth roots of unity, is 4 ζ^(⅛ Φ⁸) when β is
-- the Toffoli function's value on d, and 0 otherwise: thirty-two
-- computations.

eval⁸ : ∀ a b c d β →
        Σˡ {3} (λ g → unitˡ (phase⁸ a b c d (extend β g (suc (suc (suc zero))))
                                    (extend β g (suc (suc zero)))
                                    (extend β g (suc zero)) (extend β g zero)))
        ≡ (if β xor (d xor ((a ∧ b) ∧ c)) then 0ˡ
           else (+ 4) ·ˡ unitˡ (Φ⁸ a b c d))
eval⁸ true  true  true  true  true  = refl
eval⁸ true  true  true  true  false = refl
eval⁸ true  true  true  false true  = refl
eval⁸ true  true  true  false false = refl
eval⁸ true  true  false true  true  = refl
eval⁸ true  true  false true  false = refl
eval⁸ true  true  false false true  = refl
eval⁸ true  true  false false false = refl
eval⁸ true  false true  true  true  = refl
eval⁸ true  false true  true  false = refl
eval⁸ true  false true  false true  = refl
eval⁸ true  false true  false false = refl
eval⁸ true  false false true  true  = refl
eval⁸ true  false false true  false = refl
eval⁸ true  false false false true  = refl
eval⁸ true  false false false false = refl
eval⁸ false true  true  true  true  = refl
eval⁸ false true  true  true  false = refl
eval⁸ false true  true  false true  = refl
eval⁸ false true  true  false false = refl
eval⁸ false true  false true  true  = refl
eval⁸ false true  false true  false = refl
eval⁸ false true  false false true  = refl
eval⁸ false true  false false false = refl
eval⁸ false false true  true  true  = refl
eval⁸ false false true  true  false = refl
eval⁸ false false true  false true  = refl
eval⁸ false false true  false false = refl
eval⁸ false false false true  true  = refl
eval⁸ false false false true  false = refl
eval⁸ false false false false true  = refl
eval⁸ false false false false false = refl

private
  -- The two values of y₄: only the Toffoli function's value survives.

  outer⁸ : ∀ r sT sF (L : Lin) →
           ((if sT then ⟦ if not r then 0ˡ else L ⟧ˡ else 0ᴬ) +ᴬ
            (if sF then ⟦ if r then 0ˡ else L ⟧ˡ else 0ᴬ)) ≐
           (if (if r then sT else sF) then ⟦ L ⟧ˡ else 0ᴬ)
  outer⁸ true  true  true  L i = +-identityʳ (⟦ L ⟧ˡ i)
  outer⁸ true  true  false L i = +-identityʳ (⟦ L ⟧ˡ i)
  outer⁸ true  false true  L i = refl
  outer⁸ true  false false L i = refl
  outer⁸ false true  true  L i = +-identityˡ (⟦ L ⟧ˡ i)
  outer⁸ false false true  L i = +-identityˡ (⟦ L ⟧ˡ i)
  outer⁸ false true  false L i = refl
  outer⁸ false false false L i = refl

  if-4 : ∀ p (A : Amp) →
         (if p then (+ 4) ·ᴬ A else 0ᴬ) ≐ (+ 4) ·ᴬ (if p then A else 0ᴬ)
  if-4 true  A i = refl
  if-4 false A i = refl

  scale-four : ∀ A → (+ 4) ·ᴬ A ≐ scale 4 A
  scale-four A i = trans (sym (scale-twice 2 A i)) (scale-+ 2 2 A i)

  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
            {p p′ q q′ r r′ t t′} →
          p ≡ p′ → q ≡ q′ → r ≡ r′ → t ≡ t′ → f p q r t ≡ f p′ q′ r′ t′
  cong₄ f refl refl refl refl = refl

-- The sum over the paths from x to z: the paths split by y₄, and each
-- half is computed by PathSum.Maslov.Eighths.

Σ-paths⁸ : (a b c d : Fin n) (x z : Assign n) →
           Σᴮ (term⁴ a b c d x z) ≐
           (if same (toffoli₄ a b c d x) z
            then ⟦ (+ 4) ·ˡ unitˡ (Φ⁸ (x a) (x b) (x c) (x d)) ⟧ˡ else 0ᴬ)
Σ-paths⁸ a b c d x z i = trans
  (cong₂ _+_ (half true i) (half false i))
  (trans (outer⁸ r (s true) (s false) L i)
         (cong (λ β → (if β then ⟦ L ⟧ˡ else 0ᴬ) i) (select s r)))
  where
  r : Bool
  r = x d xor ((x a ∧ x b) ∧ x c)

  s : Bool → Bool
  s β = same (x [ d ≔ β ]) z

  L : Lin
  L = (+ 4) ·ˡ unitˡ (Φ⁸ (x a) (x b) (x c) (x d))

  -- The phase reads the path only through its values.

  resp : ∀ β → Respectsᴮ (λ g → J⁸ a b c d x (extend β g))
  resp β {g} {g′} h = trans (J⁸-def a b c d x (extend β g))
    (trans (cong₄ (phase⁸ (x a) (x b) (x c) (x d))
                  (e (suc (suc (suc zero)))) (e (suc (suc zero)))
                  (e (suc zero)) (e zero))
           (sym (J⁸-def a b c d x (extend β g′))))
    where
    e = extend-≗ β h

  half : ∀ β →
         Σᴮ (λ g → if s β then zpow (⅛ * J⁸ a b c d x (extend β g)) else 0ᴬ)
         ≐ (if s β then ⟦ if β xor r then 0ˡ else L ⟧ˡ else 0ᴬ)
  half β =
    ≐-sym (if-Σᴮ (s β) (λ g → zpow (⅛ * J⁸ a b c d x (extend β g))))
    ∙ if-cong {p = s β} refl
        (Σᴮ-ˡ (λ g → J⁸ a b c d x (extend β g)) (resp β)
         ∙ (λ j → cong (λ l → ⟦ l ⟧ˡ j)
             (trans (Σˡ-cong (λ g → cong unitˡ
                               (J⁸-def a b c d x (extend β g))))
                    (eval⁸ (x a) (x b) (x c) (x d) β))))


------------------------------------------------------------------------
-- The theorem

-- The last steps, for any values: the combination 4 ζ^(⅛ Φ) at the
-- guard is √2⁴ times ζ^φ times the basis column, when ⅛ Φ = φ.  (Proved
-- with the values abstract, so that the lemmas of other modules it uses
-- are compared with this module's terms where nothing unfolds far.)

private
  finish⁴ : (u z : Assign n) (Φ φ : ℤ) → ⅛ * Φ ≡ φ → (k : ℕ) → 4 ≡ k →
            (if same u z then ⟦ (+ 4) ·ˡ unitˡ Φ ⟧ˡ else 0ᴬ) ≐
            scale k (rot φ (δ u z))
  finish⁴ u z Φ φ eq k refl =
    if-cong {p = same u z} refl
      (⟦·ˡ⟧ (+ 4) (unitˡ Φ) ∙ (λ i → cong ((+ 4) *_) (unit-ok Φ i)))
    ∙ if-4 (same u z) (zpow (⅛ * Φ))
    ∙ (λ i → cong ((+ 4) *_)
         ((if-cong {p = same u z} refl
             (zpow-≡ (trans eq (sym (+-identityʳ φ))))
           ∙ ≐-sym (rot-if (same u z) φ 0ℤ)) i))
    ∙ scale-four (rot φ (δ u z))

-- The gate computes the three-control Toffoli function up to the
-- relative phase ¼ x_a x_b + ¼ x_a x_b x_c + ½ x_a x_b x_d: its
-- unnormalised amplitude from x to z is √2⁴ times ζ to that phase when
-- z = x[d ≔ x_d ⊕ x_a x_b x_c], and 0 otherwise.

rc3x-up-to : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d) (c≢d : c ≢ d) →
             ⟦ rc3x a b c d a≢d b≢d c≢d ⟧
               computes toffoli₄ a b c d up-to rc3x-phase a b c d
rc3x-up-to a b c d a≢d b≢d c≢d =
  computing-up-to λ x z →
  rc3x-amp a b c d a≢d b≢d c≢d x z
  ∙ Σ-paths⁸ a b c d x z
  ∙ finish⁴ (toffoli₄ a b c d x) z (Φ⁸ (x a) (x b) (x c) (x d))
            (rc3x-phase a b c d x) (Φ⁸-ok (x a) (x b) (x c) (x d))
            (norm (rc3x a b c d a≢d b≢d c≢d)) refl

-- So its path-sum is the explicit one: a diagonal phase, then the
-- three-control Toffoli permutation.

rc3x-spec : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d) (c≢d : c ≢ d) →
            ⟦ rc3x a b c d a≢d b≢d c≢d ⟧ ≋ rc3xˢ a b c d
rc3x-spec a b c d a≢d b≢d c≢d =
  up-to⇒≋phased _ (rc3xᴾ a b c d) (setWire d (liftᵉ (toffoli₄ᵉ a b c d)))
    (up-to-phase _ (λ x → ≡ᴺ-≡ (sym (eval-rc3xᴾ a b c d x)))
      (up-to-≗ _ (λ x w → sym (fun-setWireᵉ d (toffoli₄ᵉ a b c d) x w))
        (rc3x-up-to a b c d a≢d b≢d c≢d)))

-- And the phase is not trivial: the gate does not compute the
-- three-control Toffoli function exactly -- at x_a = x_b = x_c = 1,
-- x_d = 0 its amplitude to the Toffoli image is -√2⁴, where the
-- Toffoli-4 gate has √2⁴.  Stated through PathSum.Classical's record
-- rather than as ¬ (⟦ rc3x … ⟧ ≋ toffoli₄ˢ …), for the reason given
-- above; the two are equivalent (PathSum.Classical.computes⇒≋classical
-- and, for any path-sum, ≋toffoli₄⇒computes).

≋toffoli₄⇒computes : {k m : ℕ} (ξ : PathSum n k m) (a b c d : Fin n) →
                     ξ ≋ toffoli₄ˢ a b c d → ξ computes toffoli₄ a b c d
≋toffoli₄⇒computes ξ a b c d eq =
  computes-≗ ξ (λ y w → fun-setWireᵉ d (toffoli₄ᵉ a b c d) y w)
    (≋classical⇒computes ξ (setWire d (liftᵉ (toffoli₄ᵉ a b c d))) eq)

private
  1≢-1 : ¬ (1ℤ ≡ - 1ℤ)
  1≢-1 ()

rc3x-not-toffoli : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
                   (c≢d : c ≢ d) →
                   ¬ (⟦ rc3x a b c d a≢d b≢d c≢d ⟧ computes toffoli₄ a b c d)
rc3x-not-toffoli {n} a b c d a≢d b≢d c≢d exactly =
  1≢-1 (trans (sym zpow0-at-0) (trans (flip 0ᶠ) (cong -_ zpow0-at-0)))
  where
  x : Assign n
  x = (λ _ → true) [ d ≔ false ]

  φ : ℤ
  φ = rc3x-phase a b c d x

  value : φ + 0ℤ ≡ 0ℤ + ½
  value = trans
    (cong (_+ 0ℤ) (phase-at₄ a b c d x
      (≔-there (λ _ → true) false a≢d) (≔-there (λ _ → true) false b≢d)
      (≔-there (λ _ → true) false c≢d) (≔-here (λ _ → true) d false)))
    (trans (cong₂ (λ p q → p + p + q + 0ℤ) (*-identityʳ ¼) (*-zeroʳ ½))
      (trans (+-identityʳ (¼ + ¼ + 0ℤ))
        (trans (+-identityʳ (¼ + ¼)) (trans ¼+¼ (sym (+-identityˡ ½))))))

  flip : zpow 0ℤ ≐ (λ i → - zpow 0ℤ i)
  flip = up-to-exact _ exactly (rc3x-up-to a b c d a≢d b≢d c≢d) x
         ∙ (λ i → trans (cong (λ e → zpow e i) value) (zpow-anti 0ℤ i))


------------------------------------------------------------------------
-- The gate undone

-- Its inverse, the mirror image with every gate inverted, is a
-- different circuit: in the middle part the T gates now come before
-- their CNOTs.

rc3x-† : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d) (c≢d : c ≢ d) →
         rc3x a b c d a≢d b≢d c≢d † ≡
         H d ∷ R 3 d ∷ CNOT c d c≢d ∷ R† 3 d ∷ H d ∷
         R 3 d ∷ CNOT b d b≢d ∷ R† 3 d ∷ CNOT a d a≢d ∷
         R 3 d ∷ CNOT b d b≢d ∷ R† 3 d ∷ CNOT a d a≢d ∷
         H d ∷ R 3 d ∷ CNOT c d c≢d ∷ R† 3 d ∷ H d ∷ []
rc3x-† a b c d a≢d b≢d c≢d = refl

-- The function is an involution and reads assignments through their
-- values; so does the phase.

private
  xor-cancel : ∀ p q → (p xor q) xor q ≡ p
  xor-cancel false false = refl
  xor-cancel false true  = refl
  xor-cancel true  false = refl
  xor-cancel true  true  = refl

toffoli₄-involutive : (a b c d : Fin n) → a ≢ d → b ≢ d → c ≢ d →
                      (x : Assign n) →
                      ∀ u → toffoli₄ a b c d (toffoli₄ a b c d x) u ≡ x u
toffoli₄-involutive a b c d a≢d b≢d c≢d x u =
  trans (cong (λ β → ((x [ d ≔ v ]) [ d ≔ β ]) u)
              (cong₂ _xor_ (≔-here x d v)
                     (cong₂ _∧_ (cong₂ _∧_ (≔-there x v a≢d)
                                           (≔-there x v b≢d))
                                (≔-there x v c≢d))))
    (trans (≔-≔ x d v (v xor k) u)
      (trans (cong (λ β → (x [ d ≔ β ]) u) (xor-cancel (x d) k))
             (≔-self x d u)))
  where
  k v : Bool
  k = (x a ∧ x b) ∧ x c
  v = x d xor k

toffoli₄-resp : (a b c d : Fin n) → Respects-F (toffoli₄ a b c d)
toffoli₄-resp a b c d {x} {y} x≗y w =
  trans (cong (λ β → (x [ d ≔ β ]) w)
              (cong₂ _xor_ (x≗y d)
                     (cong₂ _∧_ (cong₂ _∧_ (x≗y a) (x≗y b)) (x≗y c))))
        (≔-cong d (y d xor ((y a ∧ y b) ∧ y c)) x≗y w)

rc3x-phase-resp : (a b c d : Fin n) → Respects-φ (rc3x-phase a b c d)
rc3x-phase-resp a b c d {x} {y} x≗y =
  phase-at₄ a b c d x (x≗y a) (x≗y b) (x≗y c) (x≗y d)

-- So (PathSum.RelativePhase.†-up-to) the inverse computes the same
-- permutation, up to minus the phase at the Toffoli image.

rc3x†-up-to : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
              (c≢d : c ≢ d) →
              ⟦ rc3x a b c d a≢d b≢d c≢d † ⟧
                computes toffoli₄ a b c d
                up-to (λ x → - rc3x-phase a b c d (toffoli₄ a b c d x))
rc3x†-up-to a b c d a≢d b≢d c≢d =
  †-up-to (rc3x a b c d a≢d b≢d c≢d) (rc3x-up-to a b c d a≢d b≢d c≢d)
    (toffoli₄-resp a b c d) (toffoli₄-resp a b c d)
    (rc3x-phase-resp a b c d)
    (toffoli₄-involutive a b c d a≢d b≢d c≢d)
    (toffoli₄-involutive a b c d a≢d b≢d c≢d)

-- The gate followed by its inverse computes the identity, exactly.

rc3x-rc3x† : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
             (c≢d : c ≢ d) →
             ⟦ rc3x a b c d a≢d b≢d c≢d ++ rc3x a b c d a≢d b≢d c≢d † ⟧
               computes (λ x → x)
rc3x-rc3x† a b c d a≢d b≢d c≢d =
  computes-≗ _ (toffoli₄-involutive a b c d a≢d b≢d c≢d)
    (up-to⇒computes _
      (⟦++⟧-up-to (rc3x a b c d a≢d b≢d c≢d)
                  (rc3x a b c d a≢d b≢d c≢d †)
                  (rc3x-up-to a b c d a≢d b≢d c≢d)
                  (rc3x†-up-to a b c d a≢d b≢d c≢d))
      (λ x → ≡ᴺ-≡ (trans
        (cong (λ e → rc3x-phase a b c d x + - e)
              (rc3x-phase-resp a b c d
                (toffoli₄-involutive a b c d a≢d b≢d c≢d x)))
        (+-inverseʳ (rc3x-phase a b c d x)))))

-- It has to be the inverse.  The Toffoli-4 function is an involution,
-- but the gate followed by itself -- which is how a netlist of Toffoli
-- gates would be expanded -- computes the identity only up to the phase
-- φ(x) + φ(T x), T the Toffoli-4 function and φ the relative phase;
-- at x_a = x_b = x_c = 1, x_d = 0 that is ½ + 1, so the pair is -1
-- times the identity there, and not the identity.

private
  tidy⁴ : ∀ q h → (q * 1ℤ + q * 1ℤ + h * 0ℤ) + (q * 1ℤ + q * 1ℤ + h * 1ℤ)
                  + 0ℤ ≡ (0ℤ + (q + q)) + ((q + q) + h)
  tidy⁴ = solve 2 (λ q h →
    (q :* con 1ℤ :+ q :* con 1ℤ :+ h :* con 0ℤ)
    :+ (q :* con 1ℤ :+ q :* con 1ℤ :+ h :* con 1ℤ) :+ con 0ℤ
    := (con 0ℤ :+ (q :+ q)) :+ ((q :+ q) :+ h)) refl

rc3x-rc3x-not-id : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
                   (c≢d : c ≢ d) →
                   ¬ (⟦ rc3x a b c d a≢d b≢d c≢d
                        ++ rc3x a b c d a≢d b≢d c≢d ⟧ computes (λ x → x))
rc3x-rc3x-not-id {n} a b c d a≢d b≢d c≢d exactly =
  1≢-1 (trans (sym zpow0-at-0) (trans (flip 0ᶠ) (cong -_ zpow0-at-0)))
  where
  T : Assign n → Assign n
  T = toffoli₄ a b c d

  φ : Assign n → ℤ
  φ = rc3x-phase a b c d

  -- The gate twice: the Toffoli-4 function twice, the phases added.

  twice : ⟦ rc3x a b c d a≢d b≢d c≢d ++ rc3x a b c d a≢d b≢d c≢d ⟧
            computes (λ x → x) up-to (λ x → φ x + φ (T x))
  twice = up-to-≗ _ (toffoli₄-involutive a b c d a≢d b≢d c≢d)
    (⟦++⟧-up-to (rc3x a b c d a≢d b≢d c≢d) (rc3x a b c d a≢d b≢d c≢d)
                (rc3x-up-to a b c d a≢d b≢d c≢d)
                (rc3x-up-to a b c d a≢d b≢d c≢d))

  -- The input: 1 on a, b and c, 0 on d; the gate sets d to 1.

  x₀ : Assign n
  x₀ = (λ _ → true) [ d ≔ false ]

  v₀ : Bool
  v₀ = x₀ d xor ((x₀ a ∧ x₀ b) ∧ x₀ c)

  x₀-a : x₀ a ≡ true
  x₀-a = ≔-there (λ _ → true) false a≢d

  x₀-b : x₀ b ≡ true
  x₀-b = ≔-there (λ _ → true) false b≢d

  x₀-c : x₀ c ≡ true
  x₀-c = ≔-there (λ _ → true) false c≢d

  x₀-d : x₀ d ≡ false
  x₀-d = ≔-here (λ _ → true) d false

  Tx₀-d : T x₀ d ≡ true
  Tx₀-d = trans (≔-here x₀ d v₀)
                (cong₂ _xor_ x₀-d (cong₂ _∧_ (cong₂ _∧_ x₀-a x₀-b) x₀-c))

  -- Its phase and the phase at its image: ½ and ½ + ½, which is ½
  -- modulo 1.

  sum : φ x₀ + φ (T x₀) + 0ℤ ≡ (0ℤ + ½) + 1ℤ * (+ N)
  sum = trans
    (cong₂ (λ u v → u + v + 0ℤ)
      (phase-at₄ a b c d x₀ x₀-a x₀-b x₀-c x₀-d)
      (phase-at₄ a b c d (T x₀) (trans (≔-there x₀ v₀ a≢d) x₀-a)
                 (trans (≔-there x₀ v₀ b≢d) x₀-b)
                 (trans (≔-there x₀ v₀ c≢d) x₀-c) Tx₀-d))
    (trans (tidy⁴ ¼ ½)
      (trans (cong₂ (λ u v → (0ℤ + u) + (v + ½)) ¼+¼ ¼+¼)
        (trans (cong (λ u → (0ℤ + ½) + u) ½+½)
               (cong (λ u → (0ℤ + ½) + u) (sym (*-identityˡ (+ N)))))))

  value : φ x₀ + φ (T x₀) + 0ℤ ≡ᴺ 0ℤ + ½
  value = ≡ᴺ-trans (≡ᴺ-≡ sum)
    (≡ᴺ-trans (≡ᴺ-+ (≡ᴺ-refl {0ℤ + ½}) (≡ᴺ-N 1ℤ))
              (≡ᴺ-≡ (+-identityʳ (0ℤ + ½))))

  -- So if the pair computed the identity, ζ^0 would be ζ^½ = -ζ^0.

  flip : zpow 0ℤ ≐ (λ i → - zpow 0ℤ i)
  flip = up-to-exact _ exactly twice x₀ ∙ zpow-≡ᴺ value ∙ zpow-anti 0ℤ

-- More generally: around any circuit D that computes G up to ψ and
-- leaves the values of a, b, c and d alone, the gate and its inverse
-- contribute the Toffoli permutation on either side and no phase.

rc3x-sandwich : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
                (c≢d : c ≢ d) (D : Circuit n) {G : Assign n → Assign n}
                {ψ : Assign n → ℤ} → ⟦ D ⟧ computes G up-to ψ →
                (∀ x → G x a ≡ x a) → (∀ x → G x b ≡ x b) →
                (∀ x → G x c ≡ x c) → (∀ x → G x d ≡ x d) →
                ⟦ rc3x a b c d a≢d b≢d c≢d ++ D
                  ++ rc3x a b c d a≢d b≢d c≢d † ⟧
                  computes (λ x → toffoli₄ a b c d
                                    (G (toffoli₄ a b c d x)))
                  up-to (λ x → ψ (toffoli₄ a b c d x))
rc3x-sandwich a b c d a≢d b≢d c≢d D {G} cD ga gb gc gd =
  sandwich (rc3x a b c d a≢d b≢d c≢d) D (rc3x a b c d a≢d b≢d c≢d †)
           (rc3x-up-to a b c d a≢d b≢d c≢d) cD
           (rc3x†-up-to a b c d a≢d b≢d c≢d) cancel
  where
  cancel : ∀ x → rc3x-phase a b c d x
                 + - rc3x-phase a b c d
                       (toffoli₄ a b c d (G (toffoli₄ a b c d x))) ≡ᴺ 0ℤ
  cancel x = ≡ᴺ-≡ (trans
    (cong (λ e → rc3x-phase a b c d x + - e)
          (phase-at₄ a b c d (T y) ea eb ec ed))
    (+-inverseʳ (rc3x-phase a b c d x)))
    where
    T : Assign _ → Assign _
    T = toffoli₄ a b c d

    k v : Bool
    k = (x a ∧ x b) ∧ x c
    v = x d xor k

    y : Assign _
    y = G (T x)

    ya : y a ≡ x a
    ya = trans (ga (T x)) (≔-there x v a≢d)

    yb : y b ≡ x b
    yb = trans (gb (T x)) (≔-there x v b≢d)

    yc : y c ≡ x c
    yc = trans (gc (T x)) (≔-there x v c≢d)

    ea : T y a ≡ x a
    ea = trans (≔-there y (y d xor ((y a ∧ y b) ∧ y c)) a≢d) ya

    eb : T y b ≡ x b
    eb = trans (≔-there y (y d xor ((y a ∧ y b) ∧ y c)) b≢d) yb

    ec : T y c ≡ x c
    ec = trans (≔-there y (y d xor ((y a ∧ y b) ∧ y c)) c≢d) yc

    ed : T y d ≡ x d
    ed = trans (≔-here y d (y d xor ((y a ∧ y b) ∧ y c)))
      (trans (cong₂ _xor_ (trans (gd (T x)) (≔-here x d v))
                          (cong₂ _∧_ (cong₂ _∧_ ya yb) yc))
             (xor-cancel (x d) k))
