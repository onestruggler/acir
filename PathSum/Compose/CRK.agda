------------------------------------------------------------------------
-- Presentations of groups
--
-- Definition 2.9 as the paper states it: circuits over
-- {H, CNOT, R_k, R_k†}, interpreted by composing the path-sums of
-- their gates (Amy, QPL 2018)
--
-- Definition 2.9 gives each gate a path-sum,
--
--    ⟦H⟧     = |x⟩ ↦ 1/√2 Σ_y e^(2πi xy/2) |y⟩
--    ⟦R_k⟧   = |x⟩ ↦ e^(2πi x/2^k) |x⟩
--    ⟦R_k†⟧  = |x⟩ ↦ e^(2πi (-x)/2^k) |x⟩
--    ⟦CNOT⟧  = |x₁ x₂⟩ ↦ |x₁ (x₁ ⊕ x₂)⟩ ,
--
-- and interprets a circuit by composing them, ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧,
-- leaving implicit the vertical compositions that put a gate on its
-- wires.  Here each gate acts on all n wires and the others are left
-- alone, which makes those compositions explicit: gateH w, gateR k w,
-- gateR† k w and gateCNOT c t below are the path-sums as printed, the
-- phases read with numerators over 2^M (so 1/2 is ½ = 2^(M-1) and
-- 1/2^k is 2^(M-k), as PathSum.CRK.Circuit reads R_k), the outputs the
-- inputs except on the gate's target.  CNOT's output x₁ ⊕ x₂ is the
-- Boolean polynomial x_c + x_t, read modulo 2 like every output.
-- They form a GateModel (PathSum.Compose.Gates), with the gates'
-- matrices those of PathSum.CRK.Semantics, and the compositional
-- interpretation ⟦ C ⟧ᶜ is then definition 2.9 to the letter:
-- ⟦ [] ⟧ᶜ = idPS and ⟦ g ∷ C ⟧ᶜ = ⟦ C ⟧ᶜ ∘ᴾ ⟦ g ⟧, by definition 2.6.
--
-- Proposition 2.10 for it (⟦⟧ᶜ-prop-2-10) follows from proposition
-- 2.10 for single gates, and that is where the printed path-sums are
-- checked: each is shown to have the same amplitudes as the state
-- machine of PathSum.CRK.Circuit run on that one gate (gate-≋), whose
-- matrix PathSum.CRK.Semantics computes.  The two differ as
-- polynomials -- the machine lifts linear forms (liftᴸ) and multiplies
-- by a fresh head variable (mul-y₀) -- but their phases take the same
-- values and their outputs the same bits, and that is all amplitudes
-- read (Gates.amp-ext).  So the compositional interpretation agrees
-- with the state machine, ⟦ C ⟧ᶜ ≋ ⟦ C ⟧ (⟦⟧ᶜ≋⟦⟧), and the state
-- machine satisfies the paper's clause, ⟦ C₁ ++ C₂ ⟧ ≋ ⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧
-- (⟦++⟧) -- up to ≋, for the reasons PathSum.Compose.Clifford gives.
--
-- CNOT is where definition 2.6's lifting of Boolean polynomials does
-- work.  A gate after CNOT that reads the target in its phase has the
-- lift of x_c + x_t substituted there, which is x_c + x_t - 2 x_c x_t
-- and takes the value x_c ⊕ x_t (lift-x⊕x, lemma 2.5 through
-- PathSum.Polynomial.Bind.eval-liftᴮ); substituting x_c + x_t itself
-- would give R_k after CNOT the phase 2^(M-k) · 2 on the input
-- x_c = x_t = 1, which is not 0 modulo 2^M when 2 ≤ k ≤ M.  cnot-then-R
-- evaluates the phase of R_k ∘ CNOT on the target: 2^(M-k) (x_c ⊕ x_t).
--
-- Composites of circuits are well formed (⟦∘⟧-WellFormed), through
-- ⟦++⟧ and the unit columns of PathSum.CRK.Semantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Compose.CRK (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; if_then_else_; _xor_)
open import Data.Bool.Properties using (xor-comm)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-identityʳ; *-zeroʳ; neg-distribˡ-*;
   ≤-reflexive)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (_∸_) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; head-part; tail-part)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Gates M₀ using
  (GateModel; module Compositional; ≋-amp; amp-ext; Σrot-rot; Σrot-+)
open import PathSum.Compose.Properties M₀ using (eval-∘)
open import PathSum.Compose.Sum M₀ using (_++ᵃ_)
open import PathSum.Compose.WellFormed M₀ using (WellFormed-≋)
open import PathSum.CRK.Amp M₀ using (outBit-liftᴸ)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; gateᴬ-cong; prop-2-10; ⟦⟧-unit-columns)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; extend; Σᴮ; rot)
open import PathSum.Denotation M₀ using
  (Assign; amp; outBit; _≋_; ≋-sym; outBit-μ; eval-true; eval-false;
   eval-0ᴾ-val)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Linear using
  (liftᴸ; varᴸ; wkLin; _⊕ᴸ_; mul-y₀; eval-liftᴸ; valᴸ; valᴸ-var; valᴸ-⊕;
   valᴸ-wk)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; Var; x[_]; y[_]; 0ᴾ; _+ᴾ_; _-ᴾ_; _·ᴾ_; μ; eval)
open import PathSum.Polynomial.Bind using (odd; eval-liftᴮ)
open import PathSum.Polynomial.Boolean using (liftᴮ)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ; eval-μᴾ)
open import PathSum.Polynomial.Properties using
  (valᵛ; eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-cong; eval-ext)
open import PathSum.Reduction M using (½)

private
  variable
    n m : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The gates' path-sums, as printed in definition 2.9

-- The variables on the wires after a Hadamard on w: the inputs, except
-- that w now carries the path variable y.

onWire : Fin n → Fin n → Var n 1
onWire w v = if ⌊ v Fin.≟ w ⌋ then y[ zero ] else x[ v ]

-- ⟦H⟧ = |x⟩ ↦ 1/√2 Σ_y e^(2πi xy/2) |y⟩ on wire w.

gateH : Fin n → PathSum n 1 1
gateH w = ⟨ ½ ·ᴾ (μ x[ w ] *ᴾ μ y[ zero ]) , (λ v → μ (onWire w v)) ⟩

-- ⟦R_k⟧ = |x⟩ ↦ e^(2πi x/2^k) |x⟩ and its inverse, on wire w.

gateR : ℕ → Fin n → PathSum n 0 0
gateR k w = ⟨ pow (M ∸ k) ·ᴾ μ x[ w ] , (λ v → μ x[ v ]) ⟩

gateR† : ℕ → Fin n → PathSum n 0 0
gateR† k w = ⟨ (- pow (M ∸ k)) ·ᴾ μ x[ w ] , (λ v → μ x[ v ]) ⟩

-- ⟦CNOT⟧ = |x_c x_t⟩ ↦ |x_c (x_c ⊕ x_t)⟩ with control c and target t.

gateCNOT : Fin n → Fin n → PathSum n 0 0
gateCNOT c t =
  ⟨ 0ᴾ , (λ v → if ⌊ v Fin.≟ t ⌋ then μ x[ c ] +ᴾ μ x[ t ] else μ x[ v ]) ⟩

-- The gate set's path-sums.  (CNOT's proof that c ≢ t is not needed
-- by the path-sum.)

crkGate : (g : Gate n) → PathSum n (norm (g ∷ [])) (norm (g ∷ []))
crkGate (H w)        = gateH w
crkGate (CNOT c t _) = gateCNOT c t
crkGate (R k w)      = gateR k w
crkGate (R† k w)     = gateR† k w



------------------------------------------------------------------------
-- The printed gates agree with the state machine

-- Reading bits.

private
  odd-[] : ∀ b → odd [ b ]ᶻ ≡ b
  odd-[] true  = refl
  odd-[] false = refl

  odd-sum : ∀ a b → odd ([ a ]ᶻ + [ b ]ᶻ) ≡ a xor b
  odd-sum true  true  = refl
  odd-sum true  false = refl
  odd-sum false true  = refl
  odd-sum false false = refl

  -- The assignment to no variables.

  none : Assign 0
  none ()

  ⌊≟⌋-refl : (t : Fin n) → ⌊ t Fin.≟ t ⌋ ≡ true
  ⌊≟⌋-refl t with t Fin.≟ t
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  -- Values of single variables, scaled, as monomials or as lifted
  -- forms.

  eval-μ : (v : Var n m) (x : Assign n) (y : Assign m) →
           eval (μ v) x y ≡ [ valᵛ v x y ]ᶻ
  eval-μ = eval-μᴾ

  eval-·μ : (c : ℤ) (v : Var n m) (x : Assign n) (y : Assign m) →
            eval (c ·ᴾ μ v) x y ≡ c * [ valᵛ v x y ]ᶻ
  eval-·μ c v x y = trans (eval-·ᴾ c (μ v) x y) (cong (c *_) (eval-μ v x y))

  eval-·var : (c : ℤ) (v : Var n m) (x : Assign n) (y : Assign m) →
              eval (c ·ᴾ liftᴸ (varᴸ v)) x y ≡ c * [ valᵛ v x y ]ᶻ
  eval-·var c v x y = trans (eval-·ᴾ c (liftᴸ (varᴸ v)) x y)
    (cong (c *_) (trans (eval-liftᴸ (varᴸ v) x y)
                        (cong [_]ᶻ (valᴸ-var v x y))))

  -- The sum of two variables, read modulo 2.

  odd-μ+μ : (u v : Var n m) (x : Assign n) (y : Assign m) →
            odd (eval (μ u +ᴾ μ v) x y) ≡ valᵛ u x y xor valᵛ v x y
  odd-μ+μ u v x y = trans
    (cong odd (trans (eval-+ᴾ (μ u) (μ v) x y)
                     (cong₂ _+_ (eval-μ u x y) (eval-μ v x y))))
    (odd-sum (valᵛ u x y) (valᵛ v x y))

-- R_k and R_k†.  The machine's phase is 0 plus the term the gate adds,
-- the lifted form of the wire; its outputs are the lifted inputs.

private
  R-phase : (k : ℕ) (w : Fin n) (x : Assign n) (y : Assign 0) →
            eval (phase (gateR k w)) x y ≡ eval (phase ⟦ R k w ∷ [] ⟧) x y
  R-phase k w x y = trans (eval-·μ (pow (M ∸ k)) x[ w ] x y) (sym (trans
    (eval-+ᴾ 0ᴾ (pow (M ∸ k) ·ᴾ liftᴸ (varᴸ x[ w ])) x y)
    (trans (cong₂ _+_ (eval-0ᴾ-val x y)
                      (eval-·var (pow (M ∸ k)) x[ w ] x y))
           (+-identityˡ (pow (M ∸ k) * [ x w ]ᶻ)))))

  R†-phase : (k : ℕ) (w : Fin n) (x : Assign n) (y : Assign 0) →
             eval (phase (gateR† k w)) x y ≡
             eval (phase ⟦ R† k w ∷ [] ⟧) x y
  R†-phase k w x y = trans (eval-·μ (- pow (M ∸ k)) x[ w ] x y) (sym (trans
    (eval-−ᴾ 0ᴾ (pow (M ∸ k) ·ᴾ liftᴸ (varᴸ x[ w ])) x y)
    (trans (cong₂ _-_ (eval-0ᴾ-val x y)
                      (eval-·var (pow (M ∸ k)) x[ w ] x y))
      (trans (+-identityˡ (- (pow (M ∸ k) * [ x w ]ᶻ)))
             (neg-distribˡ-* (pow (M ∸ k)) [ x w ]ᶻ)))))

  -- A gate that leaves every wire alone, in both readings.

  diag-out : ∀ {k k′} (ξ : PathSum n k 0) (ζ : PathSum n k′ 0) →
             (∀ v → out ξ v ≡ μ x[ v ]) →
             (∀ v → out ζ v ≡ liftᴸ (varᴸ x[ v ])) →
             ∀ x y v → outBit ξ x y v ≡ outBit ζ x y v
  diag-out ξ ζ h h′ x y v = trans (outBit-μ ξ x y v x[ v ] (h v))
    (sym (trans (outBit-liftᴸ ζ x y v (varᴸ x[ v ]) (h′ v))
                (valᴸ-var x[ v ] x y)))

-- CNOT.  Both phases are 0; the target reads x_c ⊕ x_t, as the sum of
-- two monomials in the printed path-sum and as the sum of two forms
-- in the machine.

private
  CNOT-out : (c t : Fin n) (p : c ≢ t) (x : Assign n) (y : Assign 0)
             (v : Fin n) →
             outBit (gateCNOT c t) x y v ≡ outBit ⟦ CNOT c t p ∷ [] ⟧ x y v
  CNOT-out c t p x y v = trans (wire ⌊ v Fin.≟ t ⌋)
    (sym (outBit-liftᴸ ⟦ CNOT c t p ∷ [] ⟧ x y v
           (if ⌊ v Fin.≟ t ⌋ then varᴸ x[ t ] ⊕ᴸ varᴸ x[ c ] else varᴸ x[ v ])
           refl))
    where
    wire : (b : Bool) →
           odd (eval (if b then μ x[ c ] +ᴾ μ x[ t ] else μ x[ v ]) x y) ≡
           valᴸ (if b then varᴸ x[ t ] ⊕ᴸ varᴸ x[ c ] else varᴸ x[ v ]) x y
    wire true  = trans (odd-μ+μ x[ c ] x[ t ] x y)
      (trans (xor-comm (x c) (x t))
        (sym (trans (valᴸ-⊕ (varᴸ x[ t ]) (varᴸ x[ c ]) x y)
                    (cong₂ _xor_ (valᴸ-var x[ t ] x y) (valᴸ-var x[ c ] x y)))))
    wire false = trans (cong odd (eval-μ x[ v ] x y))
      (trans (odd-[] (x v)) (sym (valᴸ-var x[ v ] x y)))

-- H.  The machine multiplies half the lifted input on w by a fresh head
-- variable; on each branch of that variable this is ½ x_w y.  Its
-- outputs are the lifted inputs, except the fresh variable on w.

private
  Qᴴ : Fin n → Poly n 0
  Qᴴ w = ½ ·ᴾ liftᴸ (varᴸ x[ w ])

  H-head : (w : Fin n) → ∀ γ → head-part (phase ⟦ H w ∷ [] ⟧) γ ≡ Qᴴ w γ
  H-head w (α , β) = +-identityˡ (Qᴴ w (α , β))

  H-tail : (w : Fin n) → ∀ γ → tail-part (phase ⟦ H w ∷ [] ⟧) γ ≡ 0ᴾ γ
  H-tail w (α , β) = refl

  H-machine : (w : Fin n) (x : Assign n) (b : Bool) (g : Assign 0) →
              eval (phase ⟦ H w ∷ [] ⟧) x (extend b g) ≡
              ½ * ([ x w ]ᶻ * [ b ]ᶻ)
  H-machine w x true  g = trans (eval-true (phase ⟦ H w ∷ [] ⟧) x g)
    (trans (cong₂ _+_
             (eval-ext (head-part (phase ⟦ H w ∷ [] ⟧)) (Qᴴ w) (H-head w) x g)
             (trans (eval-ext (tail-part (phase ⟦ H w ∷ [] ⟧)) 0ᴾ
                              (H-tail w) x g)
                    (eval-0ᴾ-val x g)))
      (trans (+-identityʳ (eval (Qᴴ w) x g))
        (trans (eval-·var ½ x[ w ] x g)
               (cong (½ *_) (sym (*-identityʳ [ x w ]ᶻ))))))
  H-machine w x false g = trans (eval-false (phase ⟦ H w ∷ [] ⟧) x g)
    (trans (eval-ext (tail-part (phase ⟦ H w ∷ [] ⟧)) 0ᴾ (H-tail w) x g)
      (trans (eval-0ᴾ-val x g)
        (sym (trans (cong (½ *_) (*-zeroʳ [ x w ]ᶻ)) (*-zeroʳ ½)))))

  H-phase : (w : Fin n) (x : Assign n) (y : Assign 1) →
            eval (phase (gateH w)) x y ≡ eval (phase ⟦ H w ∷ [] ⟧) x y
  H-phase w x y = trans printed (sym (trans
    (eval-cong (phase ⟦ H w ∷ [] ⟧) {x} {x} {y} {extend (y zero) (λ ())}
               (λ _ → refl) η)
    (H-machine w x (y zero) (λ ()))))
    where
    η : ∀ j → y j ≡ extend (y zero) (λ ()) j
    η zero = refl

    printed : eval (½ ·ᴾ (μ x[ w ] *ᴾ μ y[ zero ])) x y ≡
              ½ * ([ x w ]ᶻ * [ y zero ]ᶻ)
    printed = trans (eval-·ᴾ ½ (μ x[ w ] *ᴾ μ y[ zero ]) x y)
      (cong (½ *_) (trans (eval-*ᴾ (μ x[ w ]) (μ y[ zero ]) x y)
                          (cong₂ _*_ (eval-μ x[ w ] x y)
                                     (eval-μ y[ zero ] x y))))

  H-out : (w : Fin n) (x : Assign n) (y : Assign 1) (v : Fin n) →
          outBit (gateH w) x y v ≡ outBit ⟦ H w ∷ [] ⟧ x y v
  H-out w x y v =
    trans (outBit-μ (gateH w) x y v (onWire w v) refl)
      (trans (wire ⌊ v Fin.≟ w ⌋)
        (sym (outBit-liftᴸ ⟦ H w ∷ [] ⟧ x y v
               (if ⌊ v Fin.≟ w ⌋ then varᴸ y[ zero ] else wkLin (varᴸ x[ v ]))
               refl)))
    where
    wire : (b : Bool) →
           valᵛ (if b then y[ zero ] else x[ v ]) x y ≡
           valᴸ (if b then varᴸ y[ zero ] else wkLin (varᴸ x[ v ])) x y
    wire true  = sym (valᴸ-var y[ zero ] x y)
    wire false = sym (trans (valᴸ-wk (varᴸ x[ v ]) x none y (λ ()))
                            (valᴸ-var x[ v ] x none))

-- Each printed gate has the amplitudes of the state machine run on it
-- alone.

crkGate-amp≐ : (g : Gate n) (x z : Assign n) →
               amp (crkGate g) x z ≐ amp ⟦ g ∷ [] ⟧ x z
crkGate-amp≐ (H w)        = amp-ext (gateH w) ⟦ H w ∷ [] ⟧
  (H-phase w) (H-out w)
crkGate-amp≐ (CNOT c t p) = amp-ext (gateCNOT c t) ⟦ CNOT c t p ∷ [] ⟧
  (λ _ _ → refl) (CNOT-out c t p)
crkGate-amp≐ (R k w)      = amp-ext (gateR k w) ⟦ R k w ∷ [] ⟧
  (R-phase k w)
  (diag-out (gateR k w) ⟦ R k w ∷ [] ⟧ (λ _ → refl) (λ _ → refl))
crkGate-amp≐ (R† k w)     = amp-ext (gateR† k w) ⟦ R† k w ∷ [] ⟧
  (R†-phase k w)
  (diag-out (gateR† k w) ⟦ R† k w ∷ [] ⟧ (λ _ → refl) (λ _ → refl))

gate-≋ : (g : Gate n) → crkGate g ≋ ⟦ g ∷ [] ⟧
gate-≋ g = ≋-amp (crkGate g) ⟦ g ∷ [] ⟧ refl (crkGate-amp≐ g)

-- Proposition 2.10 for one printed gate.

crkGate-amp : (g : Gate n) (x z : Assign n) →
              amp (crkGate g) x z ≐ gateᴬ g (δ x) z
crkGate-amp g x z = crkGate-amp≐ g x z ∙ prop-2-10 (g ∷ []) x z


------------------------------------------------------------------------
-- The gate model

-- Each gate's matrix is built from entries of the column by rotations
-- and sums, so it is linear.

gateᴬ-lin : (g : Gate n) (e : Assign m → ℤ) (φ : Assign m → Column n)
            (z : Assign n) →
            gateᴬ g (λ w → Σᴮ (λ y → rot (e y) (φ y w))) z ≐
            Σᴮ (λ y → rot (e y) (gateᴬ g (φ y) z))
gateᴬ-lin (H w)        e φ z i = trans
  (cong (Σᴮ (λ y → rot (e y) (φ y (z [ w ≔ false ]))) i +_)
        (Σrot-rot (½ * [ z w ]ᶻ) e (λ y → φ y (z [ w ≔ true ])) i))
  (Σrot-+ e (λ y → φ y (z [ w ≔ false ]))
            (λ y → rot (½ * [ z w ]ᶻ) (φ y (z [ w ≔ true ]))) i)
gateᴬ-lin (CNOT c t p) e φ z = λ _ → refl
gateᴬ-lin (R k w)      e φ z =
  Σrot-rot (pow (M ∸ k) * [ z w ]ᶻ) e (λ y → φ y z)
gateᴬ-lin (R† k w)     e φ z =
  Σrot-rot (- (pow (M ∸ k) * [ z w ]ᶻ)) e (λ y → φ y z)

crkGates : GateModel
crkGates = record
  { G         = Gate
  ; sizeᴳ     = λ g → norm (g ∷ [])
  ; gatePS    = crkGate
  ; gateᴳ     = gateᴬ
  ; gate-amp  = crkGate-amp
  ; gate-cong = gateᴬ-cong
  ; gate-lin  = gateᴬ-lin
  }

open Compositional crkGates public


------------------------------------------------------------------------
-- Definition 2.9 compositionally

-- ⟦ g ; C ⟧ = ⟦ C ⟧ ∘ ⟦ g ⟧ with the printed ⟦ g ⟧, by definition.

⟦∷⟧ᶜ : (g : Gate n) (C : Circuit n) → ⟦ g ∷ C ⟧ᶜ ≡ (⟦ C ⟧ᶜ ∘ᴾ crkGate g)
⟦∷⟧ᶜ g C = refl

-- Its normalisation and its matrix are the circuit's.

sizeᶜ≡norm : (C : Circuit n) → sizeᶜ C ≡ norm C
sizeᶜ≡norm []               = refl
sizeᶜ≡norm (H w ∷ C)        = cong suc (sizeᶜ≡norm C)
sizeᶜ≡norm (CNOT c t p ∷ C) = sizeᶜ≡norm C
sizeᶜ≡norm (R k w ∷ C)      = sizeᶜ≡norm C
sizeᶜ≡norm (R† k w ∷ C)     = sizeᶜ≡norm C

norm-++ : (C₁ C₂ : Circuit n) → norm (C₁ ++ C₂) ≡ norm C₁ ℕ+ norm C₂
norm-++ []                C₂ = refl
norm-++ (H _ ∷ C₁)        C₂ = cong suc (norm-++ C₁ C₂)
norm-++ (CNOT _ _ _ ∷ C₁) C₂ = norm-++ C₁ C₂
norm-++ (R _ _ ∷ C₁)      C₂ = norm-++ C₁ C₂
norm-++ (R† _ _ ∷ C₁)     C₂ = norm-++ C₁ C₂

applyᴳ≡applyᴬ : (C : Circuit n) (ψ : Column n) → applyᴳ C ψ ≡ applyᴬ C ψ
applyᴳ≡applyᴬ []      ψ = refl
applyᴳ≡applyᴬ (g ∷ C) ψ = applyᴳ≡applyᴬ C (gateᴬ g ψ)

private
  applyᴳ≐applyᴬ : (C : Circuit n) (ψ : Column n) (z : Assign n) →
                  applyᴳ C ψ z ≐ applyᴬ C ψ z
  applyᴳ≐applyᴬ C ψ z i = cong (λ φ → φ z i) (applyᴳ≡applyᴬ C ψ)

-- Proposition 2.10 for definition 2.9 read compositionally.

⟦⟧ᶜ-prop-2-10 : (C : Circuit n) (x z : Assign n) →
                amp ⟦ C ⟧ᶜ x z ≐ applyᴬ C (δ x) z
⟦⟧ᶜ-prop-2-10 C x z = prop-2-10ᶜ C x z ∙ applyᴳ≐applyᴬ C (δ x) z

-- It agrees with the state machine.

⟦⟧ᶜ≋⟦⟧ : (C : Circuit n) → ⟦ C ⟧ᶜ ≋ ⟦ C ⟧
⟦⟧ᶜ≋⟦⟧ C = ≋-amp ⟦ C ⟧ᶜ ⟦ C ⟧ (sizeᶜ≡norm C)
  (λ x z → ⟦⟧ᶜ-prop-2-10 C x z ∙ ≐-sym (prop-2-10 C x z))


------------------------------------------------------------------------
-- ⟦ C₁ ; C₂ ⟧ = ⟦ C₂ ⟧ ∘ ⟦ C₁ ⟧ for the state machine

amp-⟦++⟧ : (C₁ C₂ : Circuit n) (x z : Assign n) →
           amp ⟦ C₁ ++ C₂ ⟧ x z ≐ amp (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧) x z
amp-⟦++⟧ C₁ C₂ x z =
  prop-2-10 (C₁ ++ C₂) x z
  ∙ ≐-sym (applyᴳ≐applyᴬ (C₁ ++ C₂) (δ x) z)
  ∙ ≐-sym (simulate-∘ ⟦ C₁ ⟧ ⟦ C₂ ⟧ C₁ C₂ (machine C₁) (machine C₂) x z)
  where
  machine : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴳ C (δ x) z
  machine C x z = prop-2-10 C x z ∙ ≐-sym (applyᴳ≐applyᴬ C (δ x) z)

⟦++⟧ : (C₁ C₂ : Circuit n) → ⟦ C₁ ++ C₂ ⟧ ≋ (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧)
⟦++⟧ C₁ C₂ = ≋-amp ⟦ C₁ ++ C₂ ⟧ (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧) (norm-++ C₁ C₂)
                   (amp-⟦++⟧ C₁ C₂)


------------------------------------------------------------------------
-- Where the lifting of definition 2.6 is needed

-- The target of CNOT outputs x_c ⊕ x_t, the Boolean polynomial
-- x_c + x_t.  Definition 2.6 substitutes its lift into the phase of a
-- later gate, and the lift takes the value x_c ⊕ x_t, not x_c + x_t
-- (lemma 2.5).

lift-x⊕x : (c t : Fin n) (x : Assign n) (y : Assign m) →
           eval (liftᴮ (μ x[ c ] +ᴾ μ x[ t ])) x y ≡ [ x c xor x t ]ᶻ
lift-x⊕x c t x y = trans (eval-liftᴮ (μ x[ c ] +ᴾ μ x[ t ]) x y)
  (cong [_]ᶻ (odd-μ+μ x[ c ] x[ t ] x y))

-- So R_k on the target after CNOT has the phase 2^(M-k) (x_c ⊕ x_t).

cnot-then-R : (k : ℕ) (c t : Fin n) (x : Assign n) (y : Assign 0) →
              eval (phase (gateR k t ∘ᴾ gateCNOT c t)) x y ≡
              pow (M ∸ k) * [ x c xor x t ]ᶻ
cnot-then-R k c t x y = trans
  (eval-cong (phase (gateR k t ∘ᴾ gateCNOT c t)) {x} {x} {y}
             {_++ᵃ_ {0} {0} none none} (λ _ → refl) (λ ()))
  (trans (eval-∘ (gateR k t) (gateCNOT c t) x none none)
    (trans (cong₂ _+_ (eval-0ᴾ-val x none)
                      (eval-·μ (pow (M ∸ k)) x[ t ]
                               (outBit (gateCNOT c t) x none) none))
      (trans (+-identityˡ (pow (M ∸ k) *
                           [ outBit (gateCNOT c t) x none t ]ᶻ))
             (cong (λ b → pow (M ∸ k) * [ b ]ᶻ) target))))
  where
  target : outBit (gateCNOT c t) x none t ≡ x c xor x t
  target = trans
    (cong (λ b → odd (eval (if b then μ x[ c ] +ᴾ μ x[ t ] else μ x[ t ])
                           x none))
          (⌊≟⌋-refl t))
    (odd-μ+μ x[ c ] x[ t ] x none)


------------------------------------------------------------------------
-- Composites of circuits are well formed

⟦∘⟧-WellFormed : (C₁ C₂ : Circuit n) → WellFormed (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧)
⟦∘⟧-WellFormed C₁ C₂ =
  WellFormed-≋ ⟦ C₁ ++ C₂ ⟧ (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧) (⟦++⟧ C₁ C₂)
    (λ x → ≤-reflexive (⟦⟧-unit-columns (C₁ ++ C₂) x))

⟦⟧ᶜ-WellFormed : (C : Circuit n) → WellFormed ⟦ C ⟧ᶜ
⟦⟧ᶜ-WellFormed C = WellFormed-≋ ⟦ C ⟧ ⟦ C ⟧ᶜ
  (≋-sym {ξ = ⟦ C ⟧ᶜ} {ζ = ⟦ C ⟧} (⟦⟧ᶜ≋⟦⟧ C))
  (λ x → ≤-reflexive (⟦⟧-unit-columns C x))
