------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sum of a circuit has polynomial size (Amy, QPL 2018,
-- corollary 2.15, its first half)
--
-- Corollary 2.15: "The path-sum interpretation of an n-qubit
-- Clifford+R_k circuit C has size polynomial in the volume of C
-- (n · |C|) and can be computed in polynomial time."  This module
-- proves the size half, for circuits over {H, CNOT, R_k, R_k†}
-- (PathSum.CRK.Circuit, the paper's gate set; names marked ᴷ) and over
-- {H, S, CZ} (PathSum.Circuit, definition 2.9's ⟦ C ⟧ with a path
-- variable for every Hadamard; names marked ᶜ).  The running time is
-- not formalised; PathSum.Size.Interpreter computes the representation
-- defined here gate by gate from sparse data, and bounds the size of
-- that computation's data.
--
-- What size means.  A polynomial of PathSum.Polynomial is a function
-- from all 2^(n+m) monomials to coefficients, so the Poly value that
-- ⟦ C ⟧ carries has no size to bound.  What is bounded is a
-- representation one would write down: PathSum.Size.Sparse's Rep, a
-- list of terms (monomial, coefficient in [0, 2^M)) for the phase and
-- a Z₂-linear form for each output, measured in bits (size: n + m + M
-- per term, n + m + 1 per form).  R represents ξ (Represents) when its
-- terms sum to the phase of ξ modulo 1 -- the paper's "without loss of
-- generality ... coefficients in D/Z", as e^(2πi P) reads P only
-- modulo 1 -- and each output of ξ is the lifting of its form,
-- coefficient by coefficient; PathSum.Size.Equivalence shows that
-- then ξ ≋ psʳ k R, the path-sum R stands for.  Coefficients are
-- modulo 1 of necessity: the phase of ⟦ C ⟧ can have integer
-- coefficients of degree far above d (R_3 on x₁ ⊕ x₂ ⊕ x₃ ⊕ x₄
-- contributes -x₁x₂x₃x₄), so no degree bound holds of it exactly.
--
-- The plan, which is the paper's argument made explicit.
--
--  1. Path variables.  ⟦ C ⟧ has one path variable for each Hadamard
--     (paths≡norm; norm C counts the Hadamards), so m ≤ |C|
--     (paths≤lengthᴷ, paths≤lengthᶜ).
--  2. Outputs.  Each output is the lifting of a Z₂-linear form in the
--     n + m variables, n + m + 1 bits (formsᴷ, definitionally).  Over
--     {H, S, CZ} it is a single variable v, whose monic polynomial μ v
--     is the lifting of the form v coefficient by coefficient
--     (μ-lifted, by Möbius inversion: both take the value of v).
--  3. Phase.  Proposition 2.14, with the bound it actually has
--     (PathSum.CRK.Circuit.prop-2-14-deg), makes the phase of degree
--     at most d = 2 ⊔ level C modulo 1; over {H, S, CZ}, d = 2
--     (⟦⟧-Ord≤ᶜ: every gate adds a term ¼ u or ½ u v).  So the terms on
--     the monomials of degree at most d represent it
--     (PathSum.Size.Sparse.sparse-≈), and there are at most
--     (n + m + 1)^d of them (the counting lemma,
--     PathSum.Size.Monomials.length-monomials≤).
--  4. Size.  Hence size ≤ 2 (n + |C| + M + 1)^(d+1) (repᴷ-size,
--     repᶜ-size), polynomial in n + |C| for fixed k and M, and
--     size ≤ 2 (2 n |C| + M + 1)^(d+1) in the volume when n ≥ 1 and
--     |C| ≥ 1 (repᴷ-volume, repᶜ-volume).  corollary-2-15ᴷ and
--     corollary-2-15ᶜ collect 1-4.
--
-- Remarks.  M, the precision of the phase, is the module parameter,
-- and R_k is interpreted exactly only for k ≤ M (PathSum.CRK.Circuit);
-- for a fixed k one takes M = k, and then the bound is polynomial of
-- degree max(3, k + 1): (n + |C| + 1)^max(2,k) terms, each a bit
-- vector over the n + m variables and M bits of coefficient.  For
-- Clifford+T (k = 3) the number of terms is cubic, the paper's
-- "space cubic in the volume", which counts terms.  Degree max(2, k),
-- not k, is proposition 2.14's real bound (the paper's k fails at
-- k = 1: prop-2-14-false-at-1).  The converse holds too: a
-- representation by terms of degree at most d exists only if the
-- phase has degree at most d modulo 1 (Sparse.represents-Deg≤).
--
-- The volume n · |C| of an empty circuit is 0 while its path-sum still
-- has n outputs, so read literally the paper's "polynomial in the
-- volume" fails for |C| = 0 (volume-degenerate: no bound on the size
-- by any function of the volume); the bounds here are in n + |C|, and
-- in the volume only when n, |C| ≥ 1.  The representation lists every
-- monomial of degree at most d, zero coefficients included; the paper
-- does not say how the polynomial is stored, and dropping zero terms
-- would only shorten the list.  PathSum.Size.Example computes the
-- representation of the seven-T Toffoli circuit: 26 terms, three of
-- them nonzero, 226 bits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Size (M : ℕ) where

open import Data.Fin.Base using (Fin; zero)
open import Data.Integer.Base using (ℤ; 0ℤ)
  renaming (_-_ to _-ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣-refl; 0∣⇒≡0)
open import Data.List.Base using ([]; _∷_; length)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s; >-nonZero)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (phase)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ; eval-liftᴸ; valᴸ-var)
open import PathSum.Order M using
  (Ord≤; pow; val; val-mono; pow-∣; Ord≤-+; Ord≤-0ᴾ)
open import PathSum.Polynomial using
  (Mon; Var; y[_]; ⟪_⟫; ∥_∥; _∪ᵐ_; _≟ᵐ_; _·ᴾ_; μ; eval)
open import PathSum.Polynomial.Boolean using (≈-from-values)
open import PathSum.Polynomial.Product using (eval-μᴾ)
open import PathSum.Polynomial.Properties using
  (valᵛ; i∣0; ∥⟪v⟫∥≡1; ∥∪ᵐ∥≤)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Size.Sparse M using
  (Rep; terms; Represents; Small; size; represent; represent-correct;
   represent-small; represent-length; size-bound; size-volume;
   size-forms)

import Data.Integer.Properties as ℤP
import Data.Nat.Properties as ℕ
import PathSum.Circuit
import PathSum.CRK.Circuit

private
  module K = PathSum.CRK.Circuit M
  module Q = PathSum.Circuit M

  variable
    n m : ℕ


------------------------------------------------------------------------
-- Circuits over {H, CNOT, R_k, R_k†}

-- One path variable per Hadamard, so at most |C|.

norm≤lengthᴷ : (C : K.Circuit n) → K.norm C ≤ length C
norm≤lengthᴷ []                 = z≤n
norm≤lengthᴷ (K.H _ ∷ C)        = s≤s (norm≤lengthᴷ C)
norm≤lengthᴷ (K.CNOT _ _ _ ∷ C) = ℕ.m≤n⇒m≤1+n (norm≤lengthᴷ C)
norm≤lengthᴷ (K.R _ _ ∷ C)      = ℕ.m≤n⇒m≤1+n (norm≤lengthᴷ C)
norm≤lengthᴷ (K.R† _ _ ∷ C)     = ℕ.m≤n⇒m≤1+n (norm≤lengthᴷ C)

paths≤lengthᴷ : (C : K.Circuit n) → K.paths C ≤ length C
paths≤lengthᴷ C =
  ℕ.≤-trans (ℕ.≤-reflexive (K.paths≡norm C)) (norm≤lengthᴷ C)

-- The forms on the wires once C has run.  The outputs of ⟦ C ⟧ are
-- their liftings by definition.

formsᴷ : (C : K.Circuit n) → Fin n → Lin n (K.paths C)
formsᴷ {n} C = K.sig (proj₂ (K.run C (K.init {n})))

-- The representation: the sparse phase to degree max(2, k).

repᴷ : (C : K.Circuit n) → Rep n (K.paths C)
repᴷ C = represent (2 ⊔ K.level C) K.⟦ C ⟧ (formsᴷ C)

repᴷ-represents : (C : K.Circuit n) → Represents K.⟦ C ⟧ (repᴷ C)
repᴷ-represents C = represent-correct (2 ⊔ K.level C) K.⟦ C ⟧ (formsᴷ C)
  (K.prop-2-14-deg C) (λ w γ → refl)

repᴷ-small : (C : K.Circuit n) → Small (2 ⊔ K.level C) (repᴷ C)
repᴷ-small C = represent-small (2 ⊔ K.level C) K.⟦ C ⟧ (formsᴷ C)

-- At most (n + |C| + 1)^max(2,k) terms, and size polynomial in n + |C|.

private
  1≤2⊔ : ∀ l → 1 ≤ 2 ⊔ l
  1≤2⊔ l = ℕ.≤-trans (s≤s z≤n) (ℕ.m≤m⊔n 2 l)

repᴷ-length : (C : K.Circuit n) →
              length (terms (repᴷ C)) ≤ suc (n + length C) ^ (2 ⊔ K.level C)
repᴷ-length {n} C = ℕ.≤-trans
  (represent-length (2 ⊔ K.level C) K.⟦ C ⟧ (formsᴷ C))
  (ℕ.^-monoˡ-≤ (2 ⊔ K.level C)
    (s≤s (ℕ.+-monoʳ-≤ n (paths≤lengthᴷ C))))

repᴷ-size : (C : K.Circuit n) →
            size (repᴷ C) ≤ 2 * suc (n + length C + M) ^ suc (2 ⊔ K.level C)
repᴷ-size C = size-bound (2 ⊔ K.level C) (length C) (repᴷ C)
  (1≤2⊔ (K.level C)) (paths≤lengthᴷ C)
  (represent-length (2 ⊔ K.level C) K.⟦ C ⟧ (formsᴷ C))

-- And in the volume n · |C|, when neither is 0.

repᴷ-volume : (C : K.Circuit n) → 1 ≤ n → 1 ≤ length C →
              size (repᴷ C) ≤
              2 * suc (2 * (n * length C) + M) ^ suc (2 ⊔ K.level C)
repᴷ-volume C 1≤n 1≤C = size-volume (2 ⊔ K.level C) (length C) (repᴷ C)
  (1≤2⊔ (K.level C)) (paths≤lengthᴷ C) 1≤n 1≤C
  (represent-length (2 ⊔ K.level C) K.⟦ C ⟧ (formsᴷ C))

-- Corollary 2.15, the size half.

corollary-2-15ᴷ : (C : K.Circuit n) →
  K.paths C ≡ K.norm C × K.paths C ≤ length C ×
  Represents K.⟦ C ⟧ (repᴷ C) × Small (2 ⊔ K.level C) (repᴷ C) ×
  length (terms (repᴷ C)) ≤ suc (n + length C) ^ (2 ⊔ K.level C) ×
  size (repᴷ C) ≤ 2 * suc (n + length C + M) ^ suc (2 ⊔ K.level C)
corollary-2-15ᴷ C =
  K.paths≡norm C , paths≤lengthᴷ C , repᴷ-represents C , repᴷ-small C ,
  repᴷ-length C , repᴷ-size C

-- The empty circuit on n wires has volume 0, yet any representation
-- of its path-sum has n forms: no function of the volume bounds the
-- size.

volume-degenerate : (f : ℕ → ℕ) →
  ¬ (∀ n (C : K.Circuit n) →
       ∃ λ R → Represents K.⟦ C ⟧ R × size R ≤ f (n * length C))
volume-degenerate f claim = ℕ.<-irrefl refl (ℕ.≤-trans lower upper)
  where
  w : ℕ
  w = suc (f 0)

  R : Rep w 0
  R = proj₁ (claim w [])

  lower : w ≤ size R
  lower = ℕ.≤-trans (ℕ.m≤m*n w (suc (w + 0)) {{>-nonZero (s≤s z≤n)}})
                    (size-forms R)

  upper : size R ≤ f 0
  upper = subst (λ v → size R ≤ f v) (ℕ.*-zeroʳ w)
                (proj₂ (proj₂ (claim w [])))


------------------------------------------------------------------------
-- Circuits over {H, S, CZ}

norm≤lengthᶜ : (C : Q.Circuit n) → Q.norm C ≤ length C
norm≤lengthᶜ []             = z≤n
norm≤lengthᶜ (Q.H _ ∷ C)    = s≤s (norm≤lengthᶜ C)
norm≤lengthᶜ (Q.S _ ∷ C)    = ℕ.m≤n⇒m≤1+n (norm≤lengthᶜ C)
norm≤lengthᶜ (Q.CZ _ _ ∷ C) = ℕ.m≤n⇒m≤1+n (norm≤lengthᶜ C)

paths≤lengthᶜ : (C : Q.Circuit n) → Q.pathsᵁ C ≤ length C
paths≤lengthᶜ C =
  ℕ.≤-trans (ℕ.≤-reflexive (Q.pathsᵁ≡norm C)) (norm≤lengthᶜ C)

-- The phase has order at most 2: S adds ¼ u, CZ and H add ½ u v.
-- (PathSum.Circuit proves the same of the restriction ⟦ C ⟧ᴿ; the
-- lemmas are private there and re-proved here.)

private
  Ord≤-mono : {c : ℤ} (δ : Mon n m) → pow (val 2 ∥ δ ∥) ∣ c →
              Ord≤ 2 (c ·ᴾ Q.mono δ)
  Ord≤-mono {c = c} δ h γ with γ ≟ᵐ δ
  ... | yes γ≡δ = subst (pow (val 2 ∥ γ ∥) ∣_) (sym (ℤP.*-identityʳ c))
                    (subst (λ z → pow (val 2 ∥ z ∥) ∣ c) (sym γ≡δ) h)
  ... | no  _   = subst (pow (val 2 ∥ γ ∥) ∣_) (sym (ℤP.*-zeroʳ c)) i∣0

  Ord≤-¼ : (u : Var n m) → Ord≤ 2 (¼ ·ᴾ Q.mono ⟪ u ⟫)
  Ord≤-¼ u = Ord≤-mono ⟪ u ⟫
    (subst (λ z → pow (val 2 z) ∣ ¼) (sym (∥⟪v⟫∥≡1 u)) ∣-refl)

  Ord≤-½ : (u v : Var n m) → Ord≤ 2 (½ ·ᴾ Q.mono (⟪ u ⟫ ∪ᵐ ⟪ v ⟫))
  Ord≤-½ u v = Ord≤-mono (⟪ u ⟫ ∪ᵐ ⟪ v ⟫) (pow-∣ (val-mono 2 deg))
    where
    deg : ∥ ⟪ u ⟫ ∪ᵐ ⟪ v ⟫ ∥ ≤ 2
    deg = ℕ.≤-trans (∥∪ᵐ∥≤ ⟪ u ⟫ ⟪ v ⟫)
            (ℕ.≤-reflexive (cong₂ _+_ (∥⟪v⟫∥≡1 u) (∥⟪v⟫∥≡1 v)))

  runᵁ-Ord : (C : Q.Circuit n) (st : Q.State n m) → Ord≤ 2 (Q.poly st) →
             Ord≤ 2 (Q.poly (proj₂ (Q.runᵁ C st)))
  runᵁ-Ord []             st ord = ord
  runᵁ-Ord (Q.S v ∷ C)    st ord =
    runᵁ-Ord C (Q.stepS v st) (Ord≤-+ ord (Ord≤-¼ (Q.sig st v)))
  runᵁ-Ord (Q.CZ v u ∷ C) st ord =
    runᵁ-Ord C (Q.stepCZ v u st)
      (Ord≤-+ ord (Ord≤-½ (Q.sig st v) (Q.sig st u)))
  runᵁ-Ord (Q.H v ∷ C)    st ord =
    runᵁ-Ord C (Q.allocH v st)
      (Ord≤-+ (K.Ord≤-wkPoly ord) (Ord≤-½ (Q.wkVar (Q.sig st v)) y[ zero ]))

⟦⟧-Ord≤ᶜ : (C : Q.Circuit n) → Ord≤ 2 (phase Q.⟦ C ⟧)
⟦⟧-Ord≤ᶜ C = runᵁ-Ord C Q.init Ord≤-0ᴾ

-- A single variable is a linear form: μ v and the lifting of v have
-- the same values, hence (Möbius) the same coefficients.

μ-lifted : (v : Var n m) (γ : Mon n m) → μ v γ ≡ liftᴸ (varᴸ v) γ
μ-lifted v γ = ℤP.i-j≡0⇒i≡j (μ v γ) (liftᴸ (varᴸ v) γ)
  (0∣⇒≡0 (≈-from-values {c = 0ℤ} (μ v) (liftᴸ (varᴸ v)) values γ))
  where
  values : ∀ x y → 0ℤ ∣ (eval (μ v) x y -ℤ eval (liftᴸ (varᴸ v)) x y)
  values x y = subst (0ℤ ∣_)
    (sym (trans
      (cong₂ _-ℤ_ (eval-μᴾ v x y)
                  (trans (eval-liftᴸ (varᴸ v) x y)
                         (cong [_]ᶻ (valᴸ-var v x y))))
      (ℤP.+-inverseʳ [ valᵛ v x y ]ᶻ)))
    i∣0

-- The forms: the variable on each wire.

formsᶜ : (C : Q.Circuit n) → Fin n → Lin n (Q.pathsᵁ C)
formsᶜ {n} C w = varᴸ (Q.sig (proj₂ (Q.runᵁ C (Q.init {n}))) w)

repᶜ : (C : Q.Circuit n) → Rep n (Q.pathsᵁ C)
repᶜ C = represent 2 Q.⟦ C ⟧ (formsᶜ C)

repᶜ-represents : (C : Q.Circuit n) → Represents Q.⟦ C ⟧ (repᶜ C)
repᶜ-represents {n} C = represent-correct 2 Q.⟦ C ⟧ (formsᶜ C)
  (K.Ord≤⇒Deg≤ (⟦⟧-Ord≤ᶜ C))
  (λ w γ → μ-lifted (Q.sig (proj₂ (Q.runᵁ C (Q.init {n}))) w) γ)

repᶜ-small : (C : Q.Circuit n) → Small 2 (repᶜ C)
repᶜ-small C = represent-small 2 Q.⟦ C ⟧ (formsᶜ C)

repᶜ-length : (C : Q.Circuit n) →
              length (terms (repᶜ C)) ≤ suc (n + length C) ^ 2
repᶜ-length {n} C = ℕ.≤-trans
  (represent-length 2 Q.⟦ C ⟧ (formsᶜ C))
  (ℕ.^-monoˡ-≤ 2 (s≤s (ℕ.+-monoʳ-≤ n (paths≤lengthᶜ C))))

repᶜ-size : (C : Q.Circuit n) →
            size (repᶜ C) ≤ 2 * suc (n + length C + M) ^ 3
repᶜ-size C = size-bound 2 (length C) (repᶜ C) (s≤s z≤n) (paths≤lengthᶜ C)
  (represent-length 2 Q.⟦ C ⟧ (formsᶜ C))

repᶜ-volume : (C : Q.Circuit n) → 1 ≤ n → 1 ≤ length C →
              size (repᶜ C) ≤ 2 * suc (2 * (n * length C) + M) ^ 3
repᶜ-volume C 1≤n 1≤C = size-volume 2 (length C) (repᶜ C) (s≤s z≤n)
  (paths≤lengthᶜ C) 1≤n 1≤C (represent-length 2 Q.⟦ C ⟧ (formsᶜ C))

corollary-2-15ᶜ : (C : Q.Circuit n) →
  Q.pathsᵁ C ≡ Q.norm C × Q.pathsᵁ C ≤ length C ×
  Represents Q.⟦ C ⟧ (repᶜ C) × Small 2 (repᶜ C) ×
  length (terms (repᶜ C)) ≤ suc (n + length C) ^ 2 ×
  size (repᶜ C) ≤ 2 * suc (n + length C + M) ^ 3
corollary-2-15ᶜ C =
  Q.pathsᵁ≡norm C , paths≤lengthᶜ C , repᶜ-represents C , repᶜ-small C ,
  repᶜ-length C , repᶜ-size C
