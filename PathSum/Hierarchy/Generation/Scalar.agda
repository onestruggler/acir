------------------------------------------------------------------------
-- Presentations of groups
--
-- Scalars on n qubits: what commutes with every Pauli
--
-- The preliminaries of Amy's QPL 2018 paper say that H, S (= R_2) and
-- CNOT generate the Clifford group C₂.  PathSum.Hierarchy.Circuits
-- proves one inclusion (every circuit over {H, S, CZ} is in C₂) and
-- PathSum.Hierarchy.OneQubit the other for one qubit.  This module
-- begins the other inclusion for every number n of qubits: generation
-- of C₂ modulo unitary scalars by circuits over {H, S, CZ}.
--
-- Its fact is the last step of that proof, the scalar lemma: an
-- operator V that commutes with X_j and Z_j on every wire j is a
-- scalar, V's matrix being a multiple a·I of the identity, a = V's
-- entry at |0…0⟩ (scalar-commuting; for a unitary V, fixing X_j and
-- Z_j under conjugation is the same, scalar-fixing).  The proof:
--
--   * commuting with the X_j and Z_j, V commutes with every Pauli
--     (comm-everywhere: a Pauli is a phase times a product of them,
--     PathSum.Hierarchy's Decompose);
--   * V X^y = X^y V at the entry from |0⟩ to |y⟩ says V(y, y) = V(0, 0):
--     the diagonal is constant;
--   * V Z_j = Z_j V at the entry from v to u says (-1)^(v_j) V(v, u) =
--     (-1)^(u_j) V(v, u), so V(v, u) = 0 when v and u differ at j:
--     V is diagonal.
--
-- So commuting with every Pauli and being a scalar are equivalent
-- (scalar⇔commuting), a unitary scalar is in C₂ (scalar-𝒞₂ⁿ; that a
-- unitary scalar's entry is a root of unity ζ^e is not proved, as in
-- PathSum.Hierarchy.OneQubit), and ScalarBy is OneQubit.Scalar's
-- definition, restated with this development's operators and used at
-- every n.  The module also re-exports PathSum.Hierarchy with its
-- operators and Paulis, for the modules after it (see the imports).
--
-- The plan of the generation development (package CLIFFGEN):
--
--  1. Scalars (this module).
--  2. The symplectic form (PathSum.Hierarchy.Generation.Symplectic):
--     a Pauli operator determines its data -- bits exactly, phase
--     modulo 4 -- and conjugation by a unitary preserves the
--     commutation sign ω of two Paulis; so a unitary fixing X_i and
--     Z_i sends every Pauli to one with the same bits at wire i, and
--     a Hermitian Pauli's phase is ±1.
--  3. The tableau (PathSum.Hierarchy.Generation.Tableau): an explicit,
--     computable action act of H_w, S_w and CZ_(a,b) on Pauli data,
--     phases included, with g P g† = pauli (act g p) for each gate and
--     then for every circuit (circuit-act); the bits it computes, CNOT
--     as H_t CZ_(c,t) H_t, and circuits avoiding a wire.
--  4. The synthesis (PathSum.Hierarchy.Generation.Synthesis), on Pauli
--     data only: for an anticommuting pair p, q (the images of X_w and
--     Z_w), circuits built from their bits that turn them into ±X_w
--     and ±Z_w, wire by wire, without touching wires where both are
--     trivial.
--  5. Generation (PathSum.Hierarchy.Generation): by induction on the
--     wires already fixed, a circuit C with C U fixing every X_j and
--     Z_j, whence C U is a scalar V (1) and U = C† V; with the
--     converse, C₂ modulo unitary scalars is exactly the group the
--     circuits over {H, S, CZ} generate.
--  6. The paper's gate set (PathSum.Hierarchy.Generation.CRK): the
--     same for the circuits of level ≤ 2 over {H, CNOT, R_k, R_k†},
--     by translating H, S and CZ.
--
-- The induction runs at a fixed width n: no tensor products of
-- operators and no restriction to fewer wires are needed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Generation.Scalar (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (¬∀⇒∃¬)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (*-zeroʳ; *-identityʳ; +-identityˡ)
open import Data.Product.Base using (Σ-syntax; ∃; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

import Data.Bool.Properties as Bool
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ; same; same-true; same-false)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; -ᴬ_; _≐_; Σᴮ-cong; rot; rot-map; rot-exp; rot-0; rot-anti;
   scale-injective)
  renaming (H to Hᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy.OneQubit.Code M₀ using (neg-fixed)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong)
open import PathSum.Ring.Laws M₀ using (⊛-comm)

-- The operators and the Paulis, from one application each, and the
-- lemmas of the hierarchy the development uses, re-exported: the
-- modules of the generation development each import their
-- predecessor, so that all of them state their results with the same
-- copies of the operators.  Two modules that applied
-- PathSum.Hierarchy.Operator separately would have different copies,
-- and Agda compares two spellings of a product of operators by
-- unfolding both -- in PathSum.Hierarchy.Generation that ran out of a
-- 6 GB heap.

open import PathSum.Hierarchy M₀ public using
  (IsPauli; 𝒞; module Decompose; 𝒞-resp; 𝒞-unitary; 𝒞₂-·; sign-pauli;
   conj-cong; conj-congᴾ; conj-·; conj-◃; conj-split; conj⇒intertwine;
   intertwine⇒conj)
open import PathSum.Hierarchy.Operator M₀ public
open import PathSum.Hierarchy.Pauli M₀ public

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Scalars

-- V is the scalar a: a times the identity matrix.  (This is
-- PathSum.Hierarchy.OneQubit.Scalar's ScalarBy, restated with this
-- development's operators, as are scalar-comm and scalar-conj.)

ScalarBy : Op n → Amp → Set
ScalarBy V a = ∀ x z → mat V x z ≐ (if same x z then a else 0ᴬ)

-- A scalar commutes with everything,

scalar-comm : (V : Op n) (a : Amp) → ScalarBy V a → (A : Op n) →
              V · A ≈ A · V
scalar-comm V a sV A = ≈-by (V · A) (A · V) (ℕ.+-comm (nrm V) (nrm A))
  (λ x z →
    Σᴮ-cong (λ w → ⊛-cong {a = mat A x w} ≐-refl (sV w z)
                   ∙ ⊛-if (same w z) (mat A x w) a
                   ∙ if-cong {p = same w z} {q = same z w} (same-sym w z)
                             ≐-refl)
    ∙ Σᴮ-δ z (λ w → mat A x w ⊛ a)
           (λ g h g≗h → ⊛-cong {a = mat A x g} (respᶻ A x g h g≗h) ≐-refl)
    ∙ ⊛-comm (mat A x z) a
    ∙ ≐-sym (Σᴮ-cong (λ w → ⊛-cong {a = mat V x w} (sV x w) ≐-refl
                            ∙ if-⊛ (same x w) a (mat A w z))
             ∙ Σᴮ-δ x (λ w → a ⊛ mat A w z)
                    (λ g h g≗h → ⊛-cong {a = a} ≐-refl (respˣ A z g h g≗h))))

-- so, if unitary, conjugating by it changes nothing.

scalar-conj : (V : Op n) (a : Amp) → Unitary V → ScalarBy V a →
              (P : Op n) → V · P · V † ≈ P
scalar-conj V a uV sV P =
  ·-congˡ (V †) (scalar-comm V a sV P) ⟨≈⟩ cancelʳ V P uV


------------------------------------------------------------------------
-- 𝒞 2 with this development's operators

-- PathSum.Hierarchy's types name the operators through its own
-- application of PathSum.Hierarchy.Operator; these restate the facts
-- about 𝒞 2 the development uses with the operators above, so that
-- the conversion between the two is made once, here.

𝒞₂-unitary : {U : Op n} → 𝒞 2 U → Unitary U
𝒞₂-unitary u = proj₁ u

image : (U : Op n) → 𝒞 2 U → (p : PauliData n) →
        Σ[ q ∈ PauliData n ] U · pauli p · U † ≈ pauli q
image U u p = proj₂ u p

𝒞₂-·ʰ : {U V : Op n} → 𝒞 2 U → 𝒞 2 V → 𝒞 2 (U · V)
𝒞₂-·ʰ {U = U} {V} = 𝒞₂-· {U = U} {V = V}

𝒞₂-resp : {U V : Op n} → U ≈ V → 𝒞 2 U → 𝒞 2 V
𝒞₂-resp {U = U} {V} e = 𝒞-resp 2 {U} {V} e


------------------------------------------------------------------------
-- Entries

-- Equal operators with equal normalisations have equal entries.

≈-entries : {A B : Op n} → A ≈ B → nrm A ≡ nrm B →
            ∀ x z → mat A x z ≐ mat B x z
≈-entries {A = A} {B} e eq x z =
  scale-injective (nrm A) (mat A x z) (mat B x z)
    (scale-exp (mat A x z) eq ∙ ≈-at e x z)

-- V P = P V for a Pauli P, read at the entry from v to u.

comm-entry : (V : Op n) (p : PauliData n) → V · pauli p ≈ pauli p · V →
             ∀ v u → rot (φᴾ p v) (mat V (v ⊕ᵛ xs p) u) ≐
                     rot (φᴾ p (u ⊕ᵛ xs p)) (mat V v (u ⊕ᵛ xs p))
comm-entry V p c v u =
  ≐-sym (·-pauli V p v u)
  ∙ ≈-entries {A = V · pauli p} {B = pauli p · V} c (ℕ.+-identityʳ (nrm V)) v u
  ∙ pauli-·′ p V v u


------------------------------------------------------------------------
-- Commuting with the generators is commuting with every Pauli

comm-everywhere : (V : Op n) →
                  (∀ j → V · pauli (X^ j) ≈ pauli (X^ j) · V) →
                  (∀ j → V · pauli (Z^ j) ≈ pauli (Z^ j) · V) →
                  ∀ p → V · pauli p ≈ pauli p · V
comm-everywhere {n} V cX cZ = Decompose.everywhere G G-≈ G-1 G-∙ G-i cX cZ
  where
  G : PauliData n → Set
  G p = V · pauli p ≈ pauli p · V

  G-≈ : ∀ {p q} → pauli p ≈ pauli q → G p → G q
  G-≈ {p} {q} e g = ·-congʳ V (≈-sym e) ⟨≈⟩ g ⟨≈⟩ ·-congˡ V e

  G-1 : G 1ᴾ
  G-1 = ·-congʳ V pauli-I ⟨≈⟩ ·-identityʳ V ⟨≈⟩ ≈-sym (·-identityˡ V)
        ⟨≈⟩ ·-congˡ V (≈-sym pauli-I)

  G-∙ : ∀ {p q} → G p → G q → G (p ∙ᴾ q)
  G-∙ {p} {q} gp gq =
    ·-congʳ V (≈-sym (pauli-· p q))
    ⟨≈⟩ ≈-sym (·-assoc V (pauli p) (pauli q))
    ⟨≈⟩ ·-congˡ (pauli q) gp
    ⟨≈⟩ ·-assoc (pauli p) V (pauli q)
    ⟨≈⟩ ·-congʳ (pauli p) gq
    ⟨≈⟩ ≈-sym (·-assoc (pauli p) (pauli q) V)
    ⟨≈⟩ ·-congˡ V (pauli-· p q)

  G-i : ∀ (t : ℤ) {p} → G p → G (pd (ph p + t) (xs p) (zs p))
  G-i t {p} g =
    ·-congʳ V (≈-sym (◃-pauli t p))
    ⟨≈⟩ ◃-·ʳ (¼ * t) V (pauli p)
    ⟨≈⟩ ◃-cong (¼ * t) g
    ⟨≈⟩ ≈-sym (◃-·ˡ (¼ * t) (pauli p) V)
    ⟨≈⟩ ·-congˡ V (◃-pauli t p)


------------------------------------------------------------------------
-- The scalar lemma

private
  -- The phases of X^y and of Z_j.

  φ-X : (y v : Assign n) → φᴾ (pd 0ℤ y 0ᵛ) v ≡ 0ℤ
  φ-X y v = trans (cong (λ b → ¼ * 0ℤ + ½ * [ b ]ᶻ) (dot-0ˡ 0ᵛ v (λ _ → refl)))
                  (cong₂ _+_ (*-zeroʳ ¼) (*-zeroʳ ½))

  φ-Z : (j : Fin n) (v : Assign n) → φᴾ (Z^ j) v ≡ ½ * [ v j ]ᶻ
  φ-Z j v = trans (cong (λ b → ¼ * 0ℤ + ½ * [ b ]ᶻ) (e-dot j v))
                  (trans (cong (λ t → t + ½ * [ v j ]ᶻ) (*-zeroʳ ¼))
                         (+-identityˡ (½ * [ v j ]ᶻ)))

  -- Commuting with X^y: V(y, y) = V(0, 0).

  diag : (V : Op n) → (∀ p → V · pauli p ≈ pauli p · V) →
         ∀ y → mat V y y ≐ mat V 0ᵛ 0ᵛ
  diag V c y =
    respˣ V y y (0ᵛ ⊕ᵛ y) (λ _ → refl)
    ∙ ≐-sym (rot-0 (mat V (0ᵛ ⊕ᵛ y) y))
    ∙ rot-exp {0ℤ} {φᴾ r 0ᵛ} (mat V (0ᵛ ⊕ᵛ y) y) (sym (φ-X y 0ᵛ))
    ∙ comm-entry V r (c r) 0ᵛ y
    ∙ rot-exp {φᴾ r (y ⊕ᵛ y)} {0ℤ} (mat V 0ᵛ (y ⊕ᵛ y)) (φ-X y (y ⊕ᵛ y))
    ∙ rot-0 (mat V 0ᵛ (y ⊕ᵛ y))
    ∙ respᶻ V 0ᵛ (y ⊕ᵛ y) 0ᵛ (λ j → xor-self (y j))
    where
    r = pd 0ℤ y 0ᵛ

  -- Commuting with Z_j: (-1)^(v_j) V(v, u) = (-1)^(u_j) V(v, u).

  zcomm : (V : Op n) (j : Fin n) → V · pauli (Z^ j) ≈ pauli (Z^ j) · V →
          ∀ v u → rot (½ * [ v j ]ᶻ) (mat V v u) ≐
                  rot (½ * [ u j ]ᶻ) (mat V v u)
  zcomm V j c v u =
    rot-map (½ * [ v j ]ᶻ) (respˣ V u v (v ⊕ᵛ 0ᵛ) (λ k → sym (xor-false (v k))))
    ∙ rot-exp {½ * [ v j ]ᶻ} {φᴾ (Z^ j) v} (mat V (v ⊕ᵛ 0ᵛ) u) (sym (φ-Z j v))
    ∙ comm-entry V (Z^ j) c v u
    ∙ rot-exp {φᴾ (Z^ j) (u ⊕ᵛ 0ᵛ)} {½ * [ u j ]ᶻ} (mat V v (u ⊕ᵛ 0ᵛ))
              (trans (φ-Z j (u ⊕ᵛ 0ᵛ))
                     (cong (λ b → ½ * [ b ]ᶻ) (xor-false (u j))))
    ∙ rot-map (½ * [ u j ]ᶻ) (respᶻ V v (u ⊕ᵛ 0ᵛ) u (λ k → xor-false (u k)))

  -- An amplitude equal to its own negative is 0.

  anti : (a : Amp) → rot (½ * [ true ]ᶻ) a ≐ rot (½ * [ false ]ᶻ) a → a ≐ 0ᴬ
  anti a h i = neg-fixed (a i) (sym (step i))
    where
    step : (-ᴬ a) ≐ a
    step = ≐-sym (rot-anti 0ℤ a ∙ (λ k → cong -_ (rot-0 a k)))
           ∙ rot-exp {0ℤ + (+ Hᶻ)} {½ * [ true ]ᶻ} a
                     (sym (trans (*-identityʳ ½) (sym (+-identityˡ ½))))
           ∙ h
           ∙ rot-exp {½ * [ false ]ᶻ} {0ℤ} a (*-zeroʳ ½)
           ∙ rot-0 a

  -- Commuting with every Z_j: V is diagonal.

  offdiag : (V : Op n) → (∀ j → V · pauli (Z^ j) ≈ pauli (Z^ j) · V) →
            ∀ v u → same v u ≡ false → mat V v u ≐ 0ᴬ
  offdiag {n} V c v u h =
    from (¬∀⇒∃¬ n (λ j → v j ≡ u j) (λ j → v j Bool.≟ u j)
                (same-false v u h))
    where
    by : ∀ j a b → v j ≡ a → u j ≡ b → a ≢ b → mat V v u ≐ 0ᴬ
    by j true  true  _  _  ne = ⊥-elim (ne refl)
    by j false false _  _  ne = ⊥-elim (ne refl)
    by j true  false ea eb _  = anti (mat V v u)
      (rot-exp {½ * [ true ]ᶻ} {½ * [ v j ]ᶻ} (mat V v u)
               (cong (λ b → ½ * [ b ]ᶻ) (sym ea))
       ∙ zcomm V j (c j) v u
       ∙ rot-exp {½ * [ u j ]ᶻ} {½ * [ false ]ᶻ} (mat V v u)
                 (cong (λ b → ½ * [ b ]ᶻ) eb))
    by j false true  ea eb _  = anti (mat V v u)
      (rot-exp {½ * [ true ]ᶻ} {½ * [ u j ]ᶻ} (mat V v u)
               (cong (λ b → ½ * [ b ]ᶻ) (sym eb))
       ∙ ≐-sym (zcomm V j (c j) v u)
       ∙ rot-exp {½ * [ v j ]ᶻ} {½ * [ false ]ᶻ} (mat V v u)
                 (cong (λ b → ½ * [ b ]ᶻ) ea))

    from : ∃ (λ j → v j ≢ u j) → mat V v u ≐ 0ᴬ
    from (j , ne) = by j (v j) (u j) refl refl ne

-- An operator commuting with every Pauli is a scalar: its matrix is
-- its entry at |0…0⟩ times the identity.

scalar-of-comm : (V : Op n) → (∀ p → V · pauli p ≈ pauli p · V) →
                 ScalarBy V (mat V 0ᵛ 0ᵛ)
scalar-of-comm V c x z = at (same x z) refl
  where
  at : ∀ b → same x z ≡ b →
       mat V x z ≐ (if same x z then mat V 0ᵛ 0ᵛ else 0ᴬ)
  at true  h =
    respᶻ V x z x (λ j → sym (same-true x z h j))
    ∙ diag V c x
    ∙ if-cong {p = true} {q = same x z} (sym h) (≐-refl {a = mat V 0ᵛ 0ᵛ})
  at false h =
    offdiag V (λ j → c (Z^ j)) x z h
    ∙ if-cong {p = false} {q = same x z} (sym h) (≐-refl {a = mat V 0ᵛ 0ᵛ})

-- The scalar lemma: commuting with every X_j and every Z_j.

scalar-commuting : (V : Op n) →
                   (∀ j → V · pauli (X^ j) ≈ pauli (X^ j) · V) →
                   (∀ j → V · pauli (Z^ j) ≈ pauli (Z^ j) · V) →
                   ScalarBy V (mat V 0ᵛ 0ᵛ)
scalar-commuting V cX cZ = scalar-of-comm V (comm-everywhere V cX cZ)

-- For a unitary, fixing every X_j and Z_j under conjugation.

scalar-fixing : (V : Op n) → Unitary V →
                (∀ j → V · pauli (X^ j) · V † ≈ pauli (X^ j)) →
                (∀ j → V · pauli (Z^ j) · V † ≈ pauli (Z^ j)) →
                ScalarBy V (mat V 0ᵛ 0ᵛ)
scalar-fixing V uV fX fZ = scalar-commuting V
  (λ j → conj⇒intertwine V (pauli (X^ j)) (pauli (X^ j)) uV (fX j))
  (λ j → conj⇒intertwine V (pauli (Z^ j)) (pauli (Z^ j)) uV (fZ j))

-- Commuting with every Pauli and being a scalar are the same.

scalar⇔commuting : (V : Op n) →
                   (∀ p → V · pauli p ≈ pauli p · V) ⇔ ScalarBy V (mat V 0ᵛ 0ᵛ)
scalar⇔commuting V = mk⇔ (scalar-of-comm V)
  (λ s p → scalar-comm V (mat V 0ᵛ 0ᵛ) s (pauli p))

-- A unitary scalar is in 𝒞 2, at every n.

scalar-𝒞₂ⁿ : (V : Op n) (a : Amp) → Unitary V → ScalarBy V a → 𝒞 2 V
scalar-𝒞₂ⁿ V a uV sV = uV , λ p → p , scalar-conj V a uV sV (pauli p)
