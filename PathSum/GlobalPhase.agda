------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.1 up to a global phase (Amy, QPL 2018)
--
-- Lemma 4.1 tells whether a well-formed path-sum is the identity from
-- its isometry restriction alone.  Nothing in the argument needs the
-- diagonal entries to be 1 rather than some other power ζ^e of the
-- root of unity: a column of norm at most 1 whose diagonal entry has
-- norm 1 leaves nothing for the entries off the diagonal.  The paper
-- needs this generalisation without stating it.  Its example B.1 is
-- the identity (SH)³ = ω I from which section 3.2 derives the [ω]
-- rule, and the reduction ends at the global phase ω|x⟩, not at |x⟩.
-- Carrying that verdict from the restriction back to the circuit, as
-- corollary 4.4 does for the identity, is lemma 4.1 at the phase ω.
--
-- The proof reduces to lemma 4.1 rather than repeating it.  twist e ξ
-- multiplies ξ by the global phase ζ^e by adding the constant e to its
-- phase polynomial.  Its amplitudes are those of ξ rotated by ζ^e
-- (amp-twist); the rotation preserves the trace-form norm, and hence
-- well-formedness (twist-WellFormed).  So ξ is the global phase ζ^e
-- exactly when twist (-e) ξ is the identity (≋-phase⇔), and ξ's
-- restriction is ζ^e exactly when that of twist (-e) ξ is 1.  This
-- gives lemma 4.1 up to a phase for any well-formed path-sum
-- (lemma-4-1-phase) and for any path-sum none of whose paths leaves
-- its input (diagonal-phase).
--
-- At a circuit, these combine exactly as lemma 4.1 does in
-- PathSum.Corollary:
--
--  * ⟦ C ⟧ is the phase ζ^e exactly when its restriction ⟦ C ⟧ᴿ is
--    (lemma-4-1-circuit-phase);
--  * a chain of rules from ⟦ C ⟧ᴿ that ends at that phase's
--    polynomials proves it (circuit-phase, with the check computed in
--    circuit-phase!);
--  * whatever chain from ⟦ C ⟧ᴿ ends without path variables, ⟦ C ⟧ is
--    the phase exactly when that end, syntactically, is
--    (corollary-4-4-phase).  This is corollary 4.4's characterisation
--    with |x⟩ ↦ |x⟩ replaced by |x⟩ ↦ ζ^e|x⟩.
--
-- Precision: ζ = e^{2πi/2^M} with M = M₀ + 3.  phasePS e is ζ^e I, so
-- the paper's ω = e^{2πi/8} is phasePS (2^M₀).
--
-- Not done: deciding whether a circuit is some global phase (an ∃ over
-- e), or deciding ⟦ C ⟧ ≋ phasePS e by corollary 4.4's reduction.  The
-- reduction theorem PathSum.Clifford.corollary-4-4 refutes only the
-- identity.  It would have to be run on the twisted restriction, whose
-- phase has order at most 2 only when the constant e does
-- (PathSum.Order).  Equivalence of two circuits up to a global phase is
-- not done either; PathSum.Miter's miter compares them exactly.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.GlobalPhase (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using
  (+-comm; +-identityʳ; +-inverseˡ; +-inverseʳ; ≤-trans; ≤-reflexive)
open import Data.Nat.Base using (zero)
open import Data.Product.Base using (_×_; _,_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (sym to ⇔-sym; trans to ⇔-trans)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (True; toWitness; ⌊_⌋)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AssignSum using (Σᶻ-cong)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS)
open import PathSum.Circuit M using (Circuit; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.CircuitSemantics M₀ using
  (⟦⟧ᴿ-restricts; ⟦⟧ᴿ-diagonal)
open import PathSum.Congruence M₀ using
  (phasePS; Phase-syntactic; phase-syntactic?; phase-syntactic-≋)
open import PathSum.Corollary M₀ using (circuit-WellFormed)
open import PathSum.Cyclotomic M₀ using
  (_≐_; 0ᴬ; zpow; rot; rot-map; rot-exp; rot-0; rot-+ᴬ; rot-comp;
   rot-zpow; rot-0ᴬ; rot-Σᴮ; √2·; √2·-map; scale; scale-map; Σᴮ-cong; c)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; ≋-trans; ≋-sym; eval-0ᴾ-val; semantics)
open import PathSum.Isometry M₀ using
  (WellFormed; Restriction-id; Diagonal; lemma-4-1; diagonal-≋)
open import PathSum.Norm M₀ using (‖‖²-cong; ‖‖²-rot)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; Mon; 1ᵐ; _≟ᵐ_; 0ᴾ; κ; μ; x[_]; _+ᴾ_; _≈[_]_; eval)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-κ)
open import PathSum.Reduction M using (_⟶*_)
open import PathSum.Syntactic M₀ using (id⇔syntactic)

import PathSum.Clifford
module Cliff = PathSum.Clifford M₀ semantics

private
  variable
    n k k′ m : ℕ


------------------------------------------------------------------------
-- Rotations

-- Multiplying by ζ^e commutes with multiplying by √2, hence with every
-- normalisation.  (PathSum.Identity proves rot-√2 privately.)

rot-√2 : ∀ e a → rot e (√2· a) ≐ √2· (rot e a)
rot-√2 e a i = trans (rot-+ᴬ e (rot (+ c) a) (rot (- (+ c)) a) i)
                     (cong₂ _+_ (swap (+ c)) (swap (- (+ c))))
  where
  swap : ∀ d → rot e (rot d a) i ≡ rot d (rot e a) i
  swap d = trans (rot-comp e d a i)
    (trans (rot-exp a (+-comm e d) i) (sym (rot-comp d e a i)))

rot-scale : ∀ e j a → rot e (scale j a) ≐ scale j (rot e a)
rot-scale e zero    a i = refl
rot-scale e (suc j) a i =
  trans (rot-√2 e (scale j a) i) (√2·-map (rot-scale e j a) i)

-- ζ^-e undoes ζ^e, on either side.  The exponents change only through
-- rot-exp, with both written out.

rot-inv : ∀ e a → rot (- e) (rot e a) ≐ a
rot-inv e a i = trans (rot-comp (- e) e a i)
  (trans (rot-exp {e = - e + e} {e′ = 0ℤ} a (+-inverseˡ e) i) (rot-0 a i))

rot-inv′ : ∀ e a → rot e (rot (- e) a) ≐ a
rot-inv′ e a i = trans (rot-comp e (- e) a i)
  (trans (rot-exp {e = e + - e} {e′ = 0ℤ} a (+-inverseʳ e) i) (rot-0 a i))


------------------------------------------------------------------------
-- A global phase, added to a path-sum

-- twist e ξ is ζ^e ξ: the same paths and outputs, each phase shifted
-- by the constant e.

twist : ℤ → PathSum n k m → PathSum n k m
twist e ξ = ⟨ phase ξ +ᴾ κ e , out ξ ⟩

-- Two path-sums over the same paths, hitting the same outputs, whose
-- phases differ by the constant e at every path: the amplitudes of
-- the second are those of the first times ζ^e.  The hits Boolean is
-- handled by a helper over any Boolean, not by `with`, since the goal
-- mentions amp.

amp-shift : (ξ : PathSum n k m) (ζ : PathSum n k′ m) (e : ℤ) →
            (∀ x y z → hits ζ x y z ≡ hits ξ x y z) →
            (∀ x y → eval (phase ζ) x y ≡ e + eval (phase ξ) x y) →
            ∀ x z → amp ζ x z ≐ rot e (amp ξ x z)
amp-shift ξ ζ e same-hits shifted x z i =
  trans (Σᴮ-cong (λ y j →
          trans (cong (λ b → (if b then zpow (eval (phase ζ) x y)
                                   else 0ᴬ) j)
                      (same-hits x y z))
                (term y (hits ξ x y z) j)) i)
        (sym (rot-Σᴮ e (λ y → if hits ξ x y z
                               then zpow (eval (phase ξ) x y)
                               else 0ᴬ) i))
  where
  term : ∀ y b → (if b then zpow (eval (phase ζ) x y) else 0ᴬ) ≐
                 rot e (if b then zpow (eval (phase ξ) x y) else 0ᴬ)
  term y true  j = trans (cong (λ v → zpow v j) (shifted x y))
                         (sym (rot-zpow e (eval (phase ξ) x y) j))
  term y false j = sym (rot-0ᴬ e j)

amp-twist : (e : ℤ) (ξ : PathSum n k m) (x z : Assign n) →
            amp (twist e ξ) x z ≐ rot e (amp ξ x z)
amp-twist e ξ = amp-shift ξ (twist e ξ) e (λ _ _ _ → refl) (λ x y →
  trans (eval-+ᴾ (phase ξ) (κ e) x y)
    (trans (cong (λ v → eval (phase ξ) x y + v) (eval-κ e x y))
           (+-comm (eval (phase ξ) x y) e)))

-- The global phase ζ^e is the identity rotated by ζ^e.

amp-phasePS : (e : ℤ) (x z : Assign n) →
              amp (phasePS e) x z ≐ rot e (amp idPS x z)
amp-phasePS e = amp-shift idPS (phasePS e) e (λ _ _ _ → refl) (λ x y →
  trans (eval-κ e x y)
    (sym (trans (cong (λ v → e + v) (eval-0ᴾ-val x y)) (+-identityʳ e))))

-- The paths of a twist are those of ξ, so a twist of a diagonal
-- path-sum is diagonal.

twist-Diagonal : (e : ℤ) (ξ : PathSum n k m) →
                 Diagonal ξ → Diagonal (twist e ξ)
twist-Diagonal e ξ D = D

-- Multiplying by ζ^e preserves the trace-form norm, so a twist of a
-- well-formed path-sum is well formed.

twist-WellFormed : (e : ℤ) (ξ : PathSum n k m) →
                   WellFormed ξ → WellFormed (twist e ξ)
twist-WellFormed e ξ wf x = ≤-trans
  (≤-reflexive (Σᶻ-cong (λ z →
    trans (‖‖²-cong (amp-twist e ξ x z)) (‖‖²-rot e (amp ξ x z)))))
  (wf x)


------------------------------------------------------------------------
-- Being a global phase is being the identity, twisted back

≋-phase⇔ : (ξ : PathSum n k m) (e : ℤ) →
           (ξ ≋ phasePS e ⇔ twist (- e) ξ ≋ idPS)
≋-phase⇔ {k = k} ξ e = mk⇔ to from
  where
  to : ξ ≋ phasePS e → twist (- e) ξ ≋ idPS
  to eq x z i =
    trans (amp-twist (- e) ξ x z i)
    (trans (rot-map (- e) (eq x z) i)
    (trans (rot-scale (- e) k (amp (phasePS e) x z) i)
           (scale-map k (λ j →
              trans (rot-map (- e) (amp-phasePS e x z) j)
                    (rot-inv e (amp idPS x z) j)) i)))

  from : twist (- e) ξ ≋ idPS → ξ ≋ phasePS e
  from eq x z i =
    trans (sym (rot-inv′ e (amp ξ x z) i))
    (trans (sym (rot-map e (amp-twist (- e) ξ x z) i))
    (trans (rot-map e (eq x z) i)
    (trans (rot-scale e k (amp idPS x z) i)
           (sym (scale-map k (amp-phasePS e x z) i)))))


------------------------------------------------------------------------
-- Lemma 4.1 up to a global phase

-- ξ|f(x,y)=x ≡ |x⟩ ↦ ζ^e|x⟩: every diagonal entry is √2^k ζ^e, the
-- amplitude ζ^e once normalised.  At e = 0 this is Restriction-id.

Restriction-phase : ℤ → PathSum n k m → Set
Restriction-phase {k = k} e ξ = ∀ x → amp ξ x x ≐ scale k (zpow e)

-- ξ's restriction is ζ^e exactly when that of twist (-e) ξ is 1.

restriction-twist : (ξ : PathSum n k m) (e : ℤ) →
                    (Restriction-id (twist (- e) ξ) ⇔
                     Restriction-phase e ξ)
restriction-twist {k = k} ξ e = mk⇔ to from
  where
  to : Restriction-id (twist (- e) ξ) → Restriction-phase e ξ
  to r x i =
    trans (sym (rot-inv′ e (amp ξ x x) i))
    (trans (sym (rot-map e (amp-twist (- e) ξ x x) i))
    (trans (rot-map e (r x) i)
    (trans (rot-scale e k (zpow 0ℤ) i)
           (scale-map k (λ j →
              trans (rot-zpow e 0ℤ j)
                    (cong (λ v → zpow v j) (+-identityʳ e))) i))))

  from : Restriction-phase e ξ → Restriction-id (twist (- e) ξ)
  from r x i =
    trans (amp-twist (- e) ξ x x i)
    (trans (rot-map (- e) (r x) i)
    (trans (rot-scale (- e) k (zpow e) i)
           (scale-map k (λ j →
              trans (rot-zpow (- e) e j)
                    (cong (λ v → zpow v j) (+-inverseˡ e))) i)))

-- Lemma 4.1 at the phase ζ^e, for a well-formed path-sum.

lemma-4-1-phase : (ξ : PathSum n k m) (e : ℤ) → WellFormed ξ →
                  (ξ ≋ phasePS e ⇔ Restriction-phase e ξ)
lemma-4-1-phase ξ e wf = ⇔-trans (≋-phase⇔ ξ e)
  (⇔-trans (lemma-4-1 (twist (- e) ξ) (twist-WellFormed (- e) ξ wf))
           (restriction-twist ξ e))

-- And for a diagonal path-sum, which needs no well-formedness.

diagonal-phase : (ξ : PathSum n k m) (e : ℤ) → Diagonal ξ →
                 (ξ ≋ phasePS e ⇔ Restriction-phase e ξ)
diagonal-phase ξ e D = ⇔-trans (≋-phase⇔ ξ e)
  (⇔-trans (diagonal-≋ (twist (- e) ξ) (twist-Diagonal (- e) ξ D))
           (restriction-twist ξ e))


------------------------------------------------------------------------
-- At a circuit

-- ⟦ C ⟧ is well formed, and ⟦ C ⟧ᴿ is diagonal with the same diagonal,
-- so the two are the same global phase or neither is.

lemma-4-1-circuit-phase : (C : Circuit n) (e : ℤ) →
                          (⟦ C ⟧ ≋ phasePS e ⇔ ⟦ C ⟧ᴿ ≋ phasePS e)
lemma-4-1-circuit-phase C e =
  ⇔-trans (lemma-4-1-phase ⟦ C ⟧ e (circuit-WellFormed C))
    (⇔-trans same-diagonal
             (⇔-sym (diagonal-phase ⟦ C ⟧ᴿ e (⟦⟧ᴿ-diagonal C))))
  where
  same-diagonal : Restriction-phase e ⟦ C ⟧ ⇔ Restriction-phase e ⟦ C ⟧ᴿ
  same-diagonal = mk⇔
    (λ r x i → trans (⟦⟧ᴿ-restricts C x i) (r x i))
    (λ r x i → trans (sym (⟦⟧ᴿ-restricts C x i)) (r x i))

-- A chain from the restriction that ends at the phase's polynomials
-- proves the circuit is that phase: proposition 3.1 along the chain,
-- then lemma 4.1 at the phase.

circuit-phase : (C : Circuit n) (e : ℤ) {ξ′ : PathSum n 0 0} →
                ⟦ C ⟧ᴿ ⟶* ξ′ → Phase-syntactic e ξ′ →
                ⟦ C ⟧ ≋ phasePS e
circuit-phase C e {ξ′} steps syn =
  Equivalence.from (lemma-4-1-circuit-phase C e)
    (≋-trans {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} {χ = phasePS e}
             (Cliff.⟶*-sound steps) (phase-syntactic-≋ e ξ′ syn))

-- With the end checked by computing its decision.

circuit-phase! : (C : Circuit n) (e : ℤ) {ξ′ : PathSum n 0 0} →
                 ⟦ C ⟧ᴿ ⟶* ξ′ → {True (phase-syntactic? e ξ′)} →
                 ⟦ C ⟧ ≋ phasePS e
circuit-phase! C e {ξ′} steps {t} =
  circuit-phase C e steps (toWitness {a? = phase-syntactic? e ξ′} t)


------------------------------------------------------------------------
-- The end of a reduction, syntactically

private
  -- Twisting by -e and comparing with 0 is comparing with e,
  -- coefficient by coefficient.

  shift-κ : ∀ (e p : ℤ) (γ : Mon n m) →
            (p + κ (- e) γ) - 0ℤ ≡ p - κ e γ
  shift-κ e p γ = at ⌊ γ ≟ᵐ 1ᵐ ⌋
    where
    at : ∀ b → (p + (if b then - e else 0ℤ)) - 0ℤ ≡
               p - (if b then e else 0ℤ)
    at true  = +-identityʳ (p + - e)
    at false = cong (_- 0ℤ) (+-identityʳ p)

  twisted⇔ : (P : Poly n m) (e : ℤ) →
             ((P +ᴾ κ (- e)) ≈[ pow M ] 0ᴾ ⇔ P ≈[ pow M ] κ e)
  twisted⇔ P e = mk⇔
    (λ h γ → subst (pow M ∣_) (shift-κ e (P γ) γ) (h γ))
    (λ h γ → subst (pow M ∣_) (sym (shift-κ e (P γ) γ)) (h γ))

-- A path-sum without path variables is the global phase ζ^e exactly
-- when it has no normalisation, outputs its inputs modulo 2 and has
-- the constant phase e modulo 2^M, coefficient by coefficient
-- (PathSum.Syntactic.id⇔syntactic, twisted).

phase⇔syntactic : (ξ : PathSum n k 0) (e : ℤ) →
                  (ξ ≋ phasePS e ⇔
                   (k ≡ 0 ×
                    (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) ×
                    phase ξ ≈[ pow M ] κ e))
phase⇔syntactic ξ e = ⇔-trans (≋-phase⇔ ξ e)
  (⇔-trans (id⇔syntactic (twist (- e) ξ)) (mk⇔
    (λ (k≡0 , outs , ph) →
       k≡0 , outs , Equivalence.to (twisted⇔ (phase ξ) e) ph)
    (λ (k≡0 , outs , ph) →
       k≡0 , outs , Equivalence.from (twisted⇔ (phase ξ) e) ph)))

-- Corollary 4.4 up to a global phase: whatever chain from ⟦ C ⟧ᴿ ends
-- without path variables, the circuit is the phase ζ^e exactly when
-- that end is syntactically |x⟩ ↦ ζ^e|x⟩.

corollary-4-4-phase : (C : Circuit n) (e : ℤ) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶* ξ′ →
  (⟦ C ⟧ ≋ phasePS e ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] κ e))
corollary-4-4-phase C e {ξ′} steps =
  ⇔-trans (lemma-4-1-circuit-phase C e)
    (⇔-trans along (phase⇔syntactic ξ′ e))
  where
  along : ⟦ C ⟧ᴿ ≋ phasePS e ⇔ ξ′ ≋ phasePS e
  along = mk⇔
    (λ eq → ≋-trans {ξ = ξ′} {ζ = ⟦ C ⟧ᴿ} {χ = phasePS e}
              (≋-sym {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} (Cliff.⟶*-sound steps)) eq)
    (λ eq → ≋-trans {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} {χ = phasePS e}
              (Cliff.⟶*-sound steps) eq)
