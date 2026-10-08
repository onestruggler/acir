------------------------------------------------------------------------
-- Presentations of groups
--
-- H, S and CZ generate the n-qubit Clifford group modulo unitary
-- scalars (Amy, QPL 2018, preliminaries)
--
-- The paper's preliminaries say that the gates H, R_k and CNOT
-- "suffice to generate C_k" for k ≤ 3; at k = 2, with S = R_2, that is
-- the classical fact that H, S and CNOT generate the Clifford group up
-- to global phases.  PathSum.Hierarchy.Circuits proved that every
-- circuit over {H, S, CZ} implements an element of C₂, and
-- PathSum.Hierarchy.OneQubit the converse for one qubit.  Here is the
-- converse for every number n of qubits (generation):
--
--    U ∈ C₂  ⟹  U ≈ ⟪ ⟦ C ⟧ ⟫ · V
--
-- for a circuit C over {H, S, CZ} (PathSum.Circuit, as
-- PathSum.Hierarchy.Circuits's Cl) and a unitary V whose matrix is a
-- multiple of the identity (ScalarBy V a, a its entry at |0…0⟩).  With
-- the converse (generated-𝒞₂: such a product is in C₂), C₂ is exactly
-- the set of the operators of the circuits times unitary scalars
-- (𝒞₂⇔generated): modulo unitary scalars, C₂ is the group the circuits
-- generate.  CZ_(a,b) is H_b CNOT_(a,b) H_b, so the same holds for
-- {H, S, CNOT}, which is how the paper states it; the gate set of the
-- development's {H, S, CZ} circuits is the one used.  That the
-- scalar's entry is a root of unity ζ^e, rather than an arbitrary
-- element of Z[ζ, 1/√2] of modulus 1, is not proved (as for one qubit,
-- PathSum.Hierarchy.OneQubit).
--
-- The proof is the symplectic reduction, at a fixed width n, wire by
-- wire from the last:
--
--   * reduce k: if U ∈ C₂ fixes X_i and Z_i under conjugation for
--     every wire i ≥ k, a circuit C makes ⟪ ⟦ C ⟧ ⟫ · U fix every X_j
--     and Z_j.  For k = 0 there is nothing to do; for k + 1, the step
--     at w = k (step) fixes w and keeps the wires above, and
--     reduce k finishes;
--   * the step: the images p, q of X_w and Z_w are Pauli data (U is in
--     C₂); they anticommute, and are trivial at every wire already
--     fixed, because conjugation by a unitary preserves the symplectic
--     form (PathSum.Hierarchy.Generation.Symplectic).  The circuits of
--     PathSum.Hierarchy.Generation.Synthesis, built from p's and q's
--     bits, bring them to X_w and Z_w up to sign, and the images being
--     Hermitian the signs are ±1, which S S or H S S H corrects.  The
--     circuits avoid the fixed wires, so those stay fixed
--     (PathSum.Hierarchy.Generation.Tableau's circuit-fix);
--   * at k = n, V = ⟪ ⟦ C ⟧ ⟫ · U fixes every X_j and Z_j, so it is a
--     scalar (PathSum.Hierarchy.Generation.Scalar), and U = C† V, C†
--     the inverse circuit of PathSum.Adjoint, which is the adjoint
--     (circuit-†).
--
-- No tensor product of operators, and no restriction to fewer wires,
-- is needed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Generation (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Integer.Base using (_*_)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (zero; _≤_; _<_; z≤n)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Cyclotomic M₀ using (Amp)
open import PathSum.RelativePhase M₀ using (_≡ᴺ_)

-- Everything of the development's earlier modules, from one chain of
-- applications (see PathSum.Hierarchy.Generation.Scalar's imports),
-- re-exported for the modules and the contract after this one.

open import PathSum.Hierarchy.Generation.Synthesis M₀ public

private
  variable
    n : ℕ

  ∧-elimˡ : ∀ a {b} → (a ∧ b) ≡ true → a ≡ true
  ∧-elimˡ true  _ = refl

  ∧-elimʳ : ∀ a {b} → (a ∧ b) ≡ true → b ≡ true
  ∧-elimʳ true  h = h


------------------------------------------------------------------------
-- Fixing a wire

-- U fixes X_i and Z_i under conjugation.

FixesAt : Op n → Fin n → Set
FixesAt U i = (U · pauli (X^ i) · U † ≈ pauli (X^ i)) ×
              (U · pauli (Z^ i) · U † ≈ pauli (Z^ i))

FixesAt-resp : {U V : Op n} → U ≈ V → (i : Fin n) → FixesAt U i →
               FixesAt V i
FixesAt-resp e i (fx , fz) = ≈-sym (conj-cong e (pauli (X^ i))) ⟨≈⟩ fx ,
                             ≈-sym (conj-cong e (pauli (Z^ i))) ⟨≈⟩ fz

-- What the step at w achieves: U fixes w, and every wire of D.

Good : (w : Fin n) (D : Fin n → Set) → Op n → Set
Good w D U = FixesAt U w × (∀ i → D i → FixesAt U i)

-- C, then D, then U.

compose : (C D : Cl.Circuit n) (U : Op n) →
          ⟪ Cl.⟦ C ++ D ⟧ ⟫ · U ≈ ⟪ Cl.⟦ D ⟧ ⟫ · (⟪ Cl.⟦ C ⟧ ⟫ · U)
compose C D U =
  ·-congˡ U (clifford-++ C D) ⟨≈⟩ ·-assoc ⟪ Cl.⟦ D ⟧ ⟫ ⟪ Cl.⟦ C ⟧ ⟫ U

-- A circuit after a Clifford is a Clifford.

after-𝒞₂ : (C : Cl.Circuit n) (U : Op n) → 𝒞 2 U → 𝒞 2 (⟪ Cl.⟦ C ⟧ ⟫ · U)
after-𝒞₂ C U u = 𝒞₂-·ʰ {U = ⟪ Cl.⟦ C ⟧ ⟫} {V = U} (circuit-𝒞₂ C) u

-- A circuit C₀, then one making the result good, make U good.

prepend : (w : Fin n) (D : Fin n → Set) (C₀ : Cl.Circuit n) (U : Op n) →
          Σ[ C ∈ Cl.Circuit n ] Good w D (⟪ Cl.⟦ C ⟧ ⟫ · (⟪ Cl.⟦ C₀ ⟧ ⟫ · U)) →
          Σ[ C ∈ Cl.Circuit n ] Good w D (⟪ Cl.⟦ C ⟧ ⟫ · U)
prepend w D C₀ U (C , fw , fD) =
  C₀ ++ C ,
  FixesAt-resp (≈-sym (compose C₀ C U)) w fw ,
  λ i d → FixesAt-resp (≈-sym (compose C₀ C U)) i (fD i d)


------------------------------------------------------------------------
-- The earlier modules' lemmas, in this module's names

-- Every application of a module copies its definitions, and a lemma's
-- type names the operators (_·_, pauli, ⟪_⟫, Cl.⟦_⟧) through the
-- copies of the module that proves it; compared with a type written
-- here, which names this module's copies, both sides are unfolded.
-- Restated once, for variables, that comparison is made once and is
-- cheap, and the step below applies only these.

private
  after′ : (C : Cl.Circuit n) (U : Op n) (s r : PauliData n) →
           U · pauli s · U † ≈ pauli r →
           (⟪ Cl.⟦ C ⟧ ⟫ · U) · pauli s · (⟪ Cl.⟦ C ⟧ ⟫ · U) † ≈
           pauli (actC C r)
  after′ = after

  fixes-after′ : (C : Cl.Circuit n) {i : Fin n} → Avoids i C →
                 (U : Op n) (r : PauliData n) → Supp i r →
                 U · pauli r · U † ≈ pauli r →
                 (⟪ Cl.⟦ C ⟧ ⟫ · U) · pauli r · (⟪ Cl.⟦ C ⟧ ⟫ · U) † ≈
                 pauli r
  fixes-after′ = fixes-after

  unitary-after : (C : Cl.Circuit n) (U : Op n) → Unitary U →
                  Unitary (⟪ Cl.⟦ C ⟧ ⟫ · U)
  unitary-after C U uU = Unitary-· ⟪ Cl.⟦ C ⟧ ⟫ U (circuit-unitary C) uU

  zero-X′ : (V : Op n) → Unitary V → (i w : Fin n) → i ≢ w →
            V · pauli (X^ i) · V † ≈ pauli (X^ i) →
            V · pauli (Z^ i) · V † ≈ pauli (Z^ i) →
            (r : PauliData n) → V · pauli (X^ w) · V † ≈ pauli r →
            Zero-at i r
  zero-X′ = conj-zero-X

  zero-Z′ : (V : Op n) → Unitary V → (i w : Fin n) → i ≢ w →
            V · pauli (X^ i) · V † ≈ pauli (X^ i) →
            V · pauli (Z^ i) · V † ≈ pauli (Z^ i) →
            (r : PauliData n) → V · pauli (Z^ w) · V † ≈ pauli r →
            Zero-at i r
  zero-Z′ = conj-zero-Z

  anti′ : (V : Op n) → Unitary V → (w : Fin n) (p q : PauliData n) →
          V · pauli (X^ w) · V † ≈ pauli p →
          V · pauli (Z^ w) · V † ≈ pauli q → ω p q ≡ true
  anti′ = conj-anti

  -- The images are Hermitian, so their signs are ±1.

  sign-X : (V : Op n) (w : Fin n) (p : PauliData n) →
           V · pauli (X^ w) · V † ≈ pauli p → XT w p →
           Σ[ s ∈ Bool ] ¼ * ph p ≡ᴺ ½ * [ s ]ᶻ
  sign-X V w p h xt =
    herm-sign p (conj-herm V (pauli (X^ w)) (pauli p) (X-herm w) h)
              (XT-dot w p xt)

  sign-Z : (V : Op n) (w : Fin n) (q : PauliData n) →
           V · pauli (Z^ w) · V † ≈ pauli q → ZT w q →
           Σ[ t ∈ Bool ] ¼ * ph q ≡ᴺ ½ * [ t ]ᶻ
  sign-Z V w q h zt =
    herm-sign q (conj-herm V (pauli (Z^ w)) (pauli q) (Z-herm w) h)
              (ZT-dot w q zt)

  ≈ᴾ⇒≈′ : {p q : PauliData n} → p ≈ᴾ q → pauli p ≈ pauli q
  ≈ᴾ⇒≈′ = ≈ᴾ⇒≈


------------------------------------------------------------------------
-- The step at wire w

-- U ∈ C₂ fixes the wires D, w not among them, and the images p, q of
-- X_w and Z_w are Pauli data: three circuits, built from their bits,
-- make U fix w and keep D (step).  Each phase is stated for variables
-- -- an operator, its images, its circuit, and the facts about them --
-- and hands the operator after its circuit to the next phase, prepend
-- composing the results.  The circuits phase1, phase2 and fixC appear
-- only as arguments, never inside a type written here: checking an
-- operator fact about such a circuit against a written type took Agda
-- about 20 s, with the circuit a variable well under one, and stated
-- once for the step's own images the facts did not fit a 6 GB heap.

private

  -- Phase 3: the images are X_w and Z_w up to sign (fin), and C keeps
  -- the wires of D.

  module Third {n : ℕ} (w : Fin n) (D : Fin n → Set)
               (D≢ : ∀ i → D i → i ≢ w) (U : Op n)
               (fixed : ∀ i → D i → FixesAt U i) (p q : PauliData n)
               (hp : U · pauli (X^ w) · U † ≈ pauli p)
               (hq : U · pauli (Z^ w) · U † ≈ pauli q)
               (C : Cl.Circuit n)
               (fin : (actC C p ≈ᴾ X^ w) × (actC C q ≈ᴾ Z^ w))
               (av : ∀ i → D i → Avoids i C) where

    result : Σ[ C′ ∈ Cl.Circuit n ] Good w D (⟪ Cl.⟦ C′ ⟧ ⟫ · U)
    result =
      C ,
      (after′ C U (X^ w) p hp ⟨≈⟩ ≈ᴾ⇒≈′ (proj₁ fin) ,
       after′ C U (Z^ w) q hq ⟨≈⟩ ≈ᴾ⇒≈′ (proj₂ fin)) ,
      λ i d →
        fixes-after′ C (av i d) U (X^ i) (supp-X i) (proj₁ (fixed i d)) ,
        fixes-after′ C (av i d) U (Z^ i) (supp-Z i) (proj₂ (fixed i d))

  -- Phase 2: after C, q is a Z at w alone and p still an X there; the
  -- images being Hermitian, their signs are ±1, which S S or H S S H
  -- (fixC) corrects.

  module Second {n : ℕ} (w : Fin n) (D : Fin n → Set)
                (D≢ : ∀ i → D i → i ≢ w) (U : Op n)
                (fixed : ∀ i → D i → FixesAt U i) (p q : PauliData n)
                (hp : U · pauli (X^ w) · U † ≈ pauli p)
                (hq : U · pauli (Z^ w) · U † ≈ pauli q)
                (C : Cl.Circuit n) (av : ∀ i → D i → Avoids i C)
                (xt : XT w (actC C p)) (zt : ZT w (actC C q)) where

    fixed₂ : ∀ i → D i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · U) i
    fixed₂ i d =
      fixes-after′ C (av i d) U (X^ i) (supp-X i) (proj₁ (fixed i d)) ,
      fixes-after′ C (av i d) U (Z^ i) (supp-Z i) (proj₂ (fixed i d))

    hp₂ = after′ C U (X^ w) p hp
    hq₂ = after′ C U (Z^ w) q hq

    sp = sign-X (⟪ Cl.⟦ C ⟧ ⟫ · U) w (actC C p) hp₂ xt
    sq = sign-Z (⟪ Cl.⟦ C ⟧ ⟫ · U) w (actC C q) hq₂ zt

    result : Σ[ C′ ∈ Cl.Circuit n ] Good w D (⟪ Cl.⟦ C′ ⟧ ⟫ · U)
    result =
      prepend w D C U
        (Third.result w D D≢ (⟪ Cl.⟦ C ⟧ ⟫ · U) fixed₂
           (actC C p) (actC C q) hp₂ hq₂
           (fixC w (proj₁ sp) (proj₁ sq))
           (fix-ok w (proj₁ sp) (proj₁ sq) (actC C p) (actC C q)
                   xt (proj₂ sp) zt (proj₂ sq))
           (λ i d → fixC-avoids (D≢ i d) (proj₁ sp) (proj₁ sq)))

  -- Phase 1: after C, p is an X at w alone (shape).  The images
  -- anticommute, so q then has a Z at w, and they are trivial at the
  -- wires of D, U being unitary and fixing them; phase2 follows.

  module First {n : ℕ} (w : Fin n) (D : Fin n → Set)
               (D≢ : ∀ i → D i → i ≢ w) (U : Op n) (uU : Unitary U)
               (fixed : ∀ i → D i → FixesAt U i) (p q : PauliData n)
               (hp : U · pauli (X^ w) · U † ≈ pauli p)
               (hq : U · pauli (Z^ w) · U † ≈ pauli q)
               (C : Cl.Circuit n)
               (av : ∀ {i} → i ≢ w → Zero-at i p → Avoids i C)
               (shape : Supp w (actC C p) × (zs (actC C p) w ≡ false))
               where

    uU₁ = unitary-after C U uU
    hp₁ = after′ C U (X^ w) p hp
    hq₁ = after′ C U (Z^ w) q hq

    zero-p : ∀ i → D i → Zero-at i p
    zero-p i d = zero-X′ U uU i w (D≢ i d) (proj₁ (fixed i d))
                         (proj₂ (fixed i d)) p hp

    fixed₁ : ∀ i → D i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · U) i
    fixed₁ i d =
      fixes-after′ C (av (D≢ i d) (zero-p i d)) U (X^ i) (supp-X i)
                   (proj₁ (fixed i d)) ,
      fixes-after′ C (av (D≢ i d) (zero-p i d)) U (Z^ i) (supp-Z i)
                   (proj₂ (fixed i d))

    both : (zs (actC C q) w ∧ xs (actC C p) w) ≡ true
    both =
      trans (sym (ω-shape w (actC C p) (actC C q) (proj₁ shape)
                          (proj₂ shape)))
            (anti′ (⟪ Cl.⟦ C ⟧ ⟫ · U) uU₁ w (actC C p) (actC C q) hp₁ hq₁)

    zq₁ : zs (actC C q) w ≡ true
    zq₁ = ∧-elimˡ (zs (actC C q) w) both

    xt₁ : XT w (actC C p)
    xt₁ = proj₁ shape , ∧-elimʳ (zs (actC C q) w) both , proj₂ shape

    zero-q₁ : ∀ i → D i → Zero-at i (actC C q)
    zero-q₁ i d =
      zero-Z′ (⟪ Cl.⟦ C ⟧ ⟫ · U) uU₁ i w (D≢ i d)
              (proj₁ (fixed₁ i d)) (proj₂ (fixed₁ i d)) (actC C q) hq₁

    result : Σ[ C′ ∈ Cl.Circuit n ] Good w D (⟪ Cl.⟦ C′ ⟧ ⟫ · U)
    result =
      prepend w D C U
        (Second.result w D D≢ (⟪ Cl.⟦ C ⟧ ⟫ · U) fixed₁
           (actC C p) (actC C q) hp₁ hq₁
           (phase2 w (actC C q))
           (λ i d → phase2-avoids w (actC C q) (D≢ i d) zq₁ (zero-q₁ i d))
           (phase2-pass w (actC C q) (actC C p) zq₁ xt₁)
           (phase2-shape w (actC C q) zq₁))

step : (w : Fin n) (D : Fin n → Set) → (∀ i → D i → i ≢ w) →
       (U : Op n) → 𝒞 2 U → (∀ i → D i → FixesAt U i) →
       Σ[ C ∈ Cl.Circuit n ] Good w D (⟪ Cl.⟦ C ⟧ ⟫ · U)
step w D D≢ U u fixed =
  First.result w D D≢ U (𝒞₂-unitary {U = U} u) fixed
    (proj₁ (image U u (X^ w))) (proj₁ (image U u (Z^ w)))
    (proj₂ (image U u (X^ w))) (proj₂ (image U u (Z^ w)))
    (phase1 w (proj₁ (image U u (X^ w))))
    (phase1-avoids w (proj₁ (image U u (X^ w))))
    (phase1-shape w (proj₁ (image U u (X^ w))))


------------------------------------------------------------------------
-- The reduction, wire by wire

-- The wires i ≥ k fixed, the step at w = k and a reduction below k
-- (rec) finish.

private
  advance : ∀ k (U : Op n) → 𝒞 2 U → (w : Fin n) → toℕ w ≡ k →
            Σ[ C ∈ Cl.Circuit n ]
              Good w (λ i → k < toℕ i) (⟪ Cl.⟦ C ⟧ ⟫ · U) →
            ((V : Op n) → 𝒞 2 V → (∀ i → k ≤ toℕ i → FixesAt V i) →
             Σ[ C ∈ Cl.Circuit n ] (∀ i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · V) i)) →
            Σ[ C ∈ Cl.Circuit n ] (∀ i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · U) i)
  advance {n} k U u w e (C₁ , fw , fD) rec =
    extend (rec (⟪ Cl.⟦ C₁ ⟧ ⟫ · U) (after-𝒞₂ C₁ U u)
                (λ i k≤i → cases i (ℕ.m≤n⇒m<n∨m≡n k≤i)))
    where
    cases : ∀ i → k < toℕ i ⊎ k ≡ toℕ i → FixesAt (⟪ Cl.⟦ C₁ ⟧ ⟫ · U) i
    cases i (inj₁ k<i) = fD i k<i
    cases i (inj₂ k≡i) = subst (FixesAt (⟪ Cl.⟦ C₁ ⟧ ⟫ · U))
                               (Fin.toℕ-injective (trans e k≡i)) fw

    extend : Σ[ C ∈ Cl.Circuit n ]
               (∀ i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · (⟪ Cl.⟦ C₁ ⟧ ⟫ · U)) i) →
             Σ[ C ∈ Cl.Circuit n ] (∀ i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · U) i)
    extend (C , g) =
      C₁ ++ C , λ i → FixesAt-resp (≈-sym (compose C₁ C U)) i (g i)

  -- The wire fromℕ< k<n is none of those above k.

  above≢ : ∀ {k} (k<n : k < n) i → k < toℕ i → i ≢ fromℕ< k<n
  above≢ k<n i lt e =
    ℕ.<-irrefl (sym (trans (cong toℕ e) (Fin.toℕ-fromℕ< k<n))) lt

-- If U ∈ C₂ fixes every wire i ≥ k, a circuit makes it fix every wire.

reduce : ∀ k (U : Op n) → 𝒞 2 U → (∀ i → k ≤ toℕ i → FixesAt U i) →
         Σ[ C ∈ Cl.Circuit n ] (∀ i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · U) i)
reduce zero U u h =
  [] , λ i → FixesAt-resp (≈-sym (·-congˡ U circuit-[] ⟨≈⟩ ·-identityˡ U))
                          i (h i z≤n)
reduce {n} (suc k) U u h = by (k ℕ.<? n)
  where
  by : Dec (k < n) →
       Σ[ C ∈ Cl.Circuit n ] (∀ i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · U) i)
  by (no k≮n) =
    reduce k U u (λ i k≤i → ⊥-elim (k≮n (ℕ.≤-<-trans k≤i (Fin.toℕ<n i))))
  by (yes k<n) =
    advance k U u (fromℕ< k<n) (Fin.toℕ-fromℕ< k<n)
      (step (fromℕ< k<n) (λ i → k < toℕ i) (above≢ k<n) U u h) (reduce k)


------------------------------------------------------------------------
-- Generation

-- A circuit making U fix every wire gives U as a circuit times a
-- unitary scalar.

private
  finish : (U : Op n) → Unitary U →
           Σ[ C ∈ Cl.Circuit n ] (∀ i → FixesAt (⟪ Cl.⟦ C ⟧ ⟫ · U) i) →
           Σ[ C ∈ Cl.Circuit n ] Σ[ V ∈ Op n ]
             (U ≈ ⟪ Cl.⟦ C ⟧ ⟫ · V) × Unitary V × ScalarBy V (mat V 0ᵛ 0ᵛ)
  finish U uU (C₀ , fix) =
    C₀ Adj.† , ⟪ Cl.⟦ C₀ ⟧ ⟫ · U ,
    ≈-sym (cancelˡ ⟪ Cl.⟦ C₀ ⟧ ⟫ U (circuit-unitary C₀))
      ⟨≈⟩ ·-congˡ (⟪ Cl.⟦ C₀ ⟧ ⟫ · U) (≈-sym (circuit-† C₀)) ,
    uV ,
    scalar-fixing (⟪ Cl.⟦ C₀ ⟧ ⟫ · U) uV (λ j → proj₁ (fix j))
                  (λ j → proj₂ (fix j))
    where
    uV : Unitary (⟪ Cl.⟦ C₀ ⟧ ⟫ · U)
    uV = Unitary-· ⟪ Cl.⟦ C₀ ⟧ ⟫ U (circuit-unitary C₀) uU

-- Every element of 𝒞 2 is the operator of a circuit over {H, S, CZ}
-- times a unitary scalar.

generation : (U : Op n) → 𝒞 2 U →
             Σ[ C ∈ Cl.Circuit n ] Σ[ V ∈ Op n ]
               (U ≈ ⟪ Cl.⟦ C ⟧ ⟫ · V) × Unitary V × ScalarBy V (mat V 0ᵛ 0ᵛ)
generation {n} U u =
  finish U (𝒞₂-unitary {U = U} u)
    (reduce n U u (λ i n≤i → ⊥-elim (ℕ.<⇒≱ (Fin.toℕ<n i) n≤i)))

-- Conversely, every such product is in 𝒞 2.

generated-𝒞₂ : (C : Cl.Circuit n) (V : Op n) (a : Amp) → Unitary V →
               ScalarBy V a → 𝒞 2 (⟪ Cl.⟦ C ⟧ ⟫ · V)
generated-𝒞₂ C V a uV sV =
  𝒞₂-·ʰ {U = ⟪ Cl.⟦ C ⟧ ⟫} {V = V} (circuit-𝒞₂ C) (scalar-𝒞₂ⁿ V a uV sV)

-- So C₂ is exactly the circuits' operators times unitary scalars.

Generated : Op n → Set
Generated {n} U = Σ[ C ∈ Cl.Circuit n ] Σ[ V ∈ Op n ]
                    (U ≈ ⟪ Cl.⟦ C ⟧ ⟫ · V) × Unitary V ×
                    ScalarBy V (mat V 0ᵛ 0ᵛ)

𝒞₂⇔generated : (U : Op n) → 𝒞 2 U ⇔ Generated U
𝒞₂⇔generated U = mk⇔ (generation U) (λ (C , V , e , uV , sV) →
  𝒞₂-resp {U = ⟪ Cl.⟦ C ⟧ ⟫ · V} {V = U} (≈-sym e)
         (generated-𝒞₂ C V (mat V 0ᵛ 0ᵛ) uV sV))
