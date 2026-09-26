------------------------------------------------------------------------
-- Presentations of groups
--
-- The final qubit permutation as a relabelling of the outputs (Amy,
-- QPL 2018, section 5.2)
--
-- Section 5.2 verifies "a circuit from [20] together with a final
-- qubit permutation correction".  PathSum.QFT reads the correction as
-- gates: QFTC n ends with the reversal of the wires, SWAPs of three
-- CNOTs each, and QFT-≋ proves ⟦ QFTC n ⟧ ≋ QFTˢ n.  The paper's table
-- of results suggests the other reading (PathSum.QFT.Count): its
-- Clifford count for the QFT is n², exactly the Hadamards and CNOTs of
-- the circuit without the SWAPs.  In a path-sum a permutation of the
-- qubits can be applied for free, by renaming the outputs, and this
-- module formalises that reading.
--
-- relabel ρ ξ is ξ with output w read off ξ's output ρ w; for a
-- bijection ρ with inverse σ its entry from x to z is ξ's entry from
-- x to z ∘ σ (amp-relabel), so it is ξ followed by the permutation
-- of the wires.  QFTʳ n is the specification with its outputs
-- reversed, and QFT₀-≋ proves ⟦ QFT₀ n ⟧ ≋ QFTʳ n for n + 1 ≤ M: the
-- circuit without its SWAPs implements the transform up to the
-- reversal of its outputs.  The proof is PathSum.QFT's, without the
-- reversal: along the path y the circuit leaves y_w on wire w with
-- phase Φ n x y (PathSum.QFT.Circuit.trace-QFT₀), which is the
-- relabelled specification at the path y read backwards.
--
-- The correction is needed: from two qubits on, the circuit without
-- it is not the transform (QFT₀-not-spec).  From x = 2^(n-1) to z = 1
-- the transform has the entry ζ^(2^(M-n) 2^(n-1)) = ζ^½ = -1, but the
-- circuit, whose output is reversed, has ζ^(2^(M-1) [z reversed]) =
-- 1, [z reversed] = 2^(n-1) being even.  (On zero and one qubits the
-- reversal is empty, and QFTC n is QFT₀ n.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.QFT.Relabel (M₀ : ℕ) where

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; fromℕ; opposite)
open import Data.Integer.Base using (0ℤ; 1ℤ; -1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; divides)
open import Data.Integer.Properties using (+-identityˡ; *-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _∸_; _≤_; s≤s; z≤n)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using (same; same-true; same-intro; same-≗)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Compose.Gates M₀ using (≋-amp)
open import PathSum.Compose.Properties M₀ using (hits-same)
open import PathSum.Compose.Sum M₀ using (bool-iff; if-cong; zpow-≡)
open import PathSum.CRK.Circuit M using (paths≡norm; ⟦_⟧; Rk-primitive)
open import PathSum.CRK.Trace M₀ using
  (≈φ; ≈v; trace; start; str; pathOf-str; pathAmp; amp-⟦⟧; Σᴮ-str;
   Σᴮ-opposite)
open import PathSum.CRK.Unitarity M₀ using (circuit-Unitary)
open import PathSum.Cyclotomic M₀ using
  (H; Amp; 0ᴬ; -ᴬ_; _≐_; Σᴮ-cong; Respects; zpow; zpow-anti; zpow-cong;
   scale-injective;
   0ᶠ; zpow0-at-0)
open import PathSum.Denotation M₀ using
  (Assign; amp; outBit; _≋_; ≋-sym; ≋-trans)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.PartialIsometry.Unitary M₀ using (Unitary; Unitary-≋)
open import PathSum.QFT M₀ using (spec-Φ)
open import PathSum.QFT.Circuit M₀ using
  (QFT₀; Φ; norm-QFT₀; trace-QFT₀)
open import PathSum.QFT.Spec M₀ using
  (bin; bin-≗; QFTˢ; amp-QFTˢ; QFTˢ-matrix)
open import PathSum.QFT.Unitary M₀ using (unit; bin-unit)
open import PathSum.Reduction M using (½)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n k m : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Relabelling the outputs

-- Output w of relabel ρ ξ is output ρ w of ξ.

relabel : (Fin n → Fin n) → PathSum n k m → PathSum n k m
relabel ρ ξ = ⟨ phase ξ , (λ w → out ξ (ρ w)) ⟩

-- Assignments compared through a bijection ρ with inverse σ.

same-relabel : (ρ σ : Fin n → Fin n) → (∀ w → ρ (σ w) ≡ w) →
               (∀ w → σ (ρ w) ≡ w) → (u v : Assign n) →
               same (λ w → u (ρ w)) v ≡ same u (λ w → v (σ w))
same-relabel ρ σ ρσ σρ u v = bool-iff
  (λ e → same-intro u (λ w → v (σ w)) (λ w →
    trans (cong u (sym (ρσ w))) (same-true (λ w → u (ρ w)) v e (σ w))))
  (λ e → same-intro (λ w → u (ρ w)) v (λ w →
    trans (same-true u (λ w → v (σ w)) e (ρ w)) (cong v (σρ w))))

-- The entry from x to z of the relabelled path-sum is ξ's entry from x
-- to z ∘ σ: ξ, then the wires permuted.

amp-relabel : (ρ σ : Fin n → Fin n) → (∀ w → ρ (σ w) ≡ w) →
              (∀ w → σ (ρ w) ≡ w) → (ξ : PathSum n k m) (x z : Assign n) →
              amp (relabel ρ ξ) x z ≐ amp ξ x (λ w → z (σ w))
amp-relabel ρ σ ρσ σρ ξ x z = Σᴮ-cong (λ y → if-cong
  (trans (hits-same (relabel ρ ξ) x y z)
    (trans (same-relabel ρ σ ρσ σρ (outBit ξ x y) z)
           (sym (hits-same ξ x y (λ w → z (σ w))))))
  (λ _ → refl))


------------------------------------------------------------------------
-- The transform with its outputs reversed

QFTʳ : (n : ℕ) → PathSum n n n
QFTʳ n = relabel opposite (QFTˢ n)

amp-QFTʳ : (x z : Assign n) →
           amp (QFTʳ n) x z ≐ amp (QFTˢ n) x (λ w → z (opposite w))
amp-QFTʳ {n} x z = amp-relabel opposite opposite
  Fin.opposite-involutive Fin.opposite-involutive (QFTˢ n) x z

-- Its matrix: e^{2πi [x][z reversed]/2^n} from x to z.

QFTʳ-matrix : (x z : Assign n) →
              amp (QFTʳ n) x z ≐
              zpow (pow (M ∸ n) * (bin x * bin (λ w → z (opposite w))))
QFTʳ-matrix x z = amp-QFTʳ x z ∙ QFTˢ-matrix x (λ w → z (opposite w))


------------------------------------------------------------------------
-- The circuit without its SWAPs

-- Path by path, after reading the path backwards; then summed.

amp-QFT₀ : ∀ n → suc n ≤ M → (x z : Assign n) →
           amp ⟦ QFT₀ n ⟧ x z ≐ amp (QFTʳ n) x z
amp-QFT₀ n le x z =
  amp-⟦⟧ (QFT₀ n) x z
  ∙ Σᴮ-str (trans (paths≡norm (QFT₀ n)) (norm-QFT₀ n)) (pathAmp (QFT₀ n) x z)
  ∙ Σᴮ-cong per-path
  ∙ Σᴮ-opposite G resp
  ∙ ≐-sym (amp-QFTˢ x (λ w → z (opposite w)))
  ∙ ≐-sym (amp-QFTʳ x z)
  where
  G : Assign n → Amp
  G y = if same y (λ w → z (opposite w))
        then zpow (pow (M ∸ n) * (bin x * bin y)) else 0ᴬ

  resp : Respects G
  resp g h g≗h = if-cong
    (same-≗ {x = g} {x′ = h} {z = λ w → z (opposite w)}
            {z′ = λ w → z (opposite w)} g≗h (λ _ → refl))
    (zpow-≡ (cong (λ c → pow (M ∸ n) * (bin x * c)) (bin-≗ g≗h)))

  per-path : (y : Assign n) →
             pathAmp (QFT₀ n) x z (str y) ≐ G (λ i → y (opposite i))
  per-path y = if-cong guard (λ i →
    trans (zpow-≡ {a = proj₁ (trace (QFT₀ n) (str y) (start x))}
                  {b = 0ℤ + Φ n x (str y)} (≈φ t) i)
      (trans (zpow-≡ {a = 0ℤ + Φ n x (str y)} {b = Φ n x (str y)}
                     (+-identityˡ (Φ n x (str y))) i)
             (sym (zpow-cong {e} {Φ n x (str y)} congr i))))
    where
    t = trace-QFT₀ n le (str y) 0ℤ x
    e = pow (M ∸ n) * (bin x * bin (λ i → y (opposite i)))

    -- Wire w ends holding y_w; so does the relabelled specification at
    -- the reversed path.

    guard : same (proj₂ (trace (QFT₀ n) (str y) (start x))) z ≡
            same (λ i → y (opposite i)) (λ w → z (opposite w))
    guard = trans
      (same-≗ {x = proj₂ (trace (QFT₀ n) (str y) (start x))} {x′ = y}
              {z = z} {z′ = z}
              (λ w → trans (≈v t w) (pathOf-str y w)) (λ _ → refl))
      (sym (trans (same-relabel opposite opposite
                     Fin.opposite-involutive Fin.opposite-involutive
                     y (λ w → z (opposite w)))
                  (same-≗ {x = y} {x′ = y}
                          {z = λ w → z (opposite (opposite w))} {z′ = z}
                          (λ _ → refl)
                          (λ w → cong z (Fin.opposite-involutive w)))))

    -- The phase is the specification's at the reversed path, mod 2^M.

    congr : pow M ∣ (e - Φ n x (str y))
    congr = Eq.subst
      (λ c → pow M ∣ (pow (M ∸ n) * (bin x * c) - Φ n x (str y)))
      (bin-≗ {n = n} (λ i → pathOf-str y (opposite i)))
      (spec-Φ n (ℕ.<⇒≤ le) x (str y))

-- The circuit without the reversal is the transform with its outputs
-- reversed.

QFT₀-≋ : ∀ n → suc n ≤ M → ⟦ QFT₀ n ⟧ ≋ QFTʳ n
QFT₀-≋ n le = ≋-amp ⟦ QFT₀ n ⟧ (QFTʳ n) (norm-QFT₀ n) (amp-QFT₀ n le)

QFT₀-matrix : ∀ n → suc n ≤ M → (x z : Assign n) →
              amp ⟦ QFT₀ n ⟧ x z ≐
              zpow (pow (M ∸ n) * (bin x * bin (λ w → z (opposite w))))
QFT₀-matrix n le x z = amp-QFT₀ n le x z ∙ QFTʳ-matrix x z

-- So QFTʳ n is unitary too.

QFTʳ-Unitary : ∀ n → suc n ≤ M → Unitary (QFTʳ n)
QFTʳ-Unitary n le =
  Unitary-≋ ⟦ QFT₀ n ⟧ (QFTʳ n) (QFT₀-≋ n le) (circuit-Unitary (QFT₀ n))


------------------------------------------------------------------------
-- The correction is needed

private
  -- ζ^½ = -1, ½ being 2^(M-1) = H.

  zpow-½ : zpow ½ ≐ -ᴬ zpow 0ℤ
  zpow-½ i = trans (zpow-≡ {a = ½} {b = 0ℤ + (+ H)} refl i) (zpow-anti 0ℤ i)

  1≢-1 : ¬ (1ℤ ≡ -1ℤ)
  1≢-1 ()

  -- From x = 2^(n-1) to z = 1 the transform has the entry ζ^½ = -1,
  -- the transform with reversed outputs ζ^(2^M B) = 1.  (The size is
  -- written out as suc (suc m) throughout: a local name for it would
  -- make Agda compare path-sums of the circuit by unfolding them.)

  not-spec : ∀ m → suc (suc (suc m)) ≤ M →
             ¬ (⟦ QFT₀ (suc (suc m)) ⟧ ≋ QFTˢ (suc (suc m)))
  not-spec m le eq = 1≢-1
    (trans (sym zpow0-at-0)
    (trans (sym (rev-entry 0ᶠ))
    (trans (same-matrix 0ᶠ)
    (trans (spec-entry 0ᶠ)
           (cong -_ zpow0-at-0)))))
    where
    x = unit {suc (suc m)} (fromℕ (suc m))
    z = unit {suc (suc m)} zero
    B = bin (λ i → z (opposite (suc i)))

    -- The two path-sums would have the same matrix: both have
    -- normalisation n.

    same-matrix : amp (QFTʳ (suc (suc m))) x z ≐ amp (QFTˢ (suc (suc m))) x z
    same-matrix = scale-injective (suc (suc m))
      (amp (QFTʳ (suc (suc m))) x z) (amp (QFTˢ (suc (suc m))) x z)
      (≋-trans {ξ = QFTʳ (suc (suc m))} {ζ = ⟦ QFT₀ (suc (suc m)) ⟧}
               {χ = QFTˢ (suc (suc m))}
               (≋-sym {ξ = ⟦ QFT₀ (suc (suc m)) ⟧} {ζ = QFTʳ (suc (suc m))}
                      (QFT₀-≋ (suc (suc m)) le))
               eq x z)

    -- 2^(M-n) · 2^(n-1) = ½.

    p·q : pow (M ∸ suc (suc m)) * pow (suc m) ≡ ½
    p·q = Rk-primitive (s≤s z≤n) (ℕ.<⇒≤ le)

    bin-x : bin x ≡ pow (suc m)
    bin-x = trans (bin-unit (fromℕ (suc m)))
                  (cong pow (Fin.toℕ-fromℕ (suc m)))

    -- The transform: ζ^(½ · 1) = -1.

    spec-entry : amp (QFTˢ (suc (suc m))) x z ≐ -ᴬ zpow 0ℤ
    spec-entry = QFTˢ-matrix x z
      ∙ zpow-≡ {a = pow (M ∸ suc (suc m)) * (bin x * bin z)} {b = ½}
          (trans (cong₂ (λ a b → pow (M ∸ suc (suc m)) * (a * b))
                        bin-x (bin-unit {suc (suc m)} zero))
            (trans (cong (pow (M ∸ suc (suc m)) *_)
                         (*-identityʳ (pow (suc m))))
                   p·q))
      ∙ zpow-½

    -- The reversed transform: the reversed z has bit 0 clear, so
    -- [z reversed] = 2 B, and the phase is ½ · 2 B = 2^M B.

    rev-entry : amp (QFTʳ (suc (suc m))) x z ≐ zpow 0ℤ
    rev-entry = QFTʳ-matrix x z
      ∙ zpow-cong
          {e = pow (M ∸ suc (suc m)) * (bin x * bin (λ w → z (opposite w)))}
          {e′ = 0ℤ} (divides B expo)
      where
      expo : pow (M ∸ suc (suc m)) * (bin x * bin (λ w → z (opposite w))) -
             0ℤ ≡ B * pow M
      expo = trans
        (cong (λ b → pow (M ∸ suc (suc m)) * (b * (0ℤ + (+ 2) * B)) - 0ℤ)
              bin-x)
        (trans (solve 3 (λ p q B →
                  p :* (q :* (con 0ℤ :+ con (+ 2) :* B)) :- con 0ℤ :=
                  B :* ((p :* q) :* con (+ 2)))
                refl (pow (M ∸ suc (suc m))) (pow (suc m)) B)
          (cong (B *_) (trans (cong (_* (+ 2)) p·q)
                              (sym (pow-suc (M ∸ 1))))))

QFT₀-not-spec : ∀ n → 2 ≤ n → suc n ≤ M → ¬ (⟦ QFT₀ n ⟧ ≋ QFTˢ n)
QFT₀-not-spec (suc (suc m)) (s≤s (s≤s z≤n)) le = not-spec m le
