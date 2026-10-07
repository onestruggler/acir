------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators on n qubits, with a normalisation, and their algebra
--
-- The preliminaries of Amy's QPL 2018 paper recall the Clifford
-- hierarchy: C₁ is the Pauli group, C_k = {U | U C₁ U† ⊆ C_(k-1)}, the
-- gates H, CNOT and R_k lie in C_k, the Clifford group is C₂, and for
-- k ≤ 3 the gates generate C_k.  "Clifford" elsewhere in PathSum is a
-- syntactic class (circuits over {H, S, CZ}, or of level ≤ 2 over
-- {H, CNOT, R_k}); the paper's C_k is semantic, a set of unitaries.
-- This module and the ones beside it formalise the hierarchy on the
-- operators the development already has.
--
-- An operator is what a path-sum or a circuit denotes: a matrix with
-- entries in Z[ζ] (PathSum.Cyclotomic, ζ = e^(2πi/2^M)) together with
-- a normalisation k, the operator being the matrix divided by √2^k.
-- The entry mat U x z is the one from input x to output z, as amp ξ x z
-- is for a path-sum, so the operator of a path-sum ξ is ⟪ ξ ⟫ and the
-- equality _≈_ of operators is definitionally PathSum.Denotation's
-- _≋_, the normalisations cleared by multiplying across.  An operator
-- carries a proof that its entries read assignments only through their
-- values, which every sum over assignments needs.  The algebra:
--
--   * the product U · V, "V, then U": the matrix product of
--     PathSum.Compose.Matrix (_⊙_), normalisations added;
--   * the adjoint U †, the conjugate transpose, with PathSum.Ring's
--     conjugation ζ ↦ ζ⁻¹;
--   * the identity I, the basis columns δ x;
--   * the scalar ζ^e ◃ U, a global phase;
--   * Unitary U, U†U = I and UU† = I.
--
-- They obey the laws of a monoid with involution up to ≈: ≈ is an
-- equivalence and a congruence for each operation, the product is
-- associative with unit I, († reverses products), phases move through
-- products and adjoints, and unitaries are closed under products,
-- adjoints and phases.  Every law is proved on entries, from the ring
-- laws of PathSum.Ring.Laws and the sums of PathSum.Compose.Sum.
--
-- The plan of the development (phase A of the hierarchy package):
--
--  1. Operators (this module).  The operators considered are those
--     with entries in Z[ζ, 1/√2].  The hierarchy defined inside that
--     universe is the paper's intersected with it: C₁ = P_n lies in
--     it, and U P U† lies in it whenever U and P do, so by induction
--     on k an operator of the universe is in the restricted C_k
--     exactly when it is in the paper's.  Nothing outside the
--     universe -- an arbitrary complex unitary -- is formalised.
--  2. The Pauli group (PathSum.Hierarchy.Pauli): i^a X^x Z^z for a
--     phase exponent a and bit vectors x, z, with its multiplication
--     and adjoint read off the data, every Pauli unitary, and two
--     Paulis commuting up to a sign.
--  3. The hierarchy (PathSum.Hierarchy): C₁ = P_n and C_(k+1) = {U
--     unitary : U P U† ∈ C_k for every P ∈ P_n}, exactly as printed;
--     invariant under ≈, increasing in k, closed under phases and
--     under multiplication by Paulis; the generator form (X_j and Z_j
--     suffice) at C₂ and C₃, where it is equivalent because C₁ and C₂
--     are closed under products; C₂ closed under products.
--  4. The gates (PathSum.Hierarchy.Gates): H and CNOT are in C₂ (and
--     so in every C_k, k ≥ 2); a diagonal phase ζ^(s·x_w) with
--     2^(M-k) | s is in C_k, so R_k and R_k† are in C_k; neither H nor
--     CNOT is in C₁, so the paper's "for k ≥ 1, all three gates lie in
--     C_k" is a slip for k ≥ 2 (R_k alone lies in C_k from k = 1); R_k
--     is not in C_(k-1) for 2 ≤ k ≤ M.
--  5. Circuits (PathSum.Hierarchy.Circuits): the operator of every
--     circuit of level ≤ 2 over {H, CNOT, R_k, R_k†}, and of every
--     circuit over {H, S, CZ}, is in C₂ -- the syntactic Clifford class
--     lies in the semantic one.  Beyond level 2 it does not: T H T has
--     level 3 and is not in C₃, so C₃ is not closed under products.
--  6. One qubit (PathSum.Hierarchy.OneQubit): every single-qubit
--     element of C₂ is, up to a global phase, one of 24 products of H
--     and S, which are pairwise distinct up to phase -- the paper's
--     "for k ≤ 3 they generate C_k" at k = 2, n = 1.  For n qubits
--     neither generation of C₂ nor anything about generating C₃ is
--     formalised, and whether C_k = ⟨H, R_k, CNOT⟩ is, as the paper
--     says, open.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Hierarchy.Operator (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣m⇒∣-m)
open import Data.Integer.Properties using (+-inverseˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using (_=ᵇ_; same; same-≗)
open import PathSum.AmpLinear M₀ using (scale-comm)
open import PathSum.Base using (PathSum)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Compose.Matrix M₀ using (_⊙_; if-⊛; ⊛-if)
open import PathSum.Compose.Properties M₀ using (amp-≗ˣ)
open import PathSum.Compose.Sum M₀ using
  (Σᴮ-swap; Σᴮ-δ; if-cong; scale-+; scale-exp; scale-rot; scale-Σᴮ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ; Σᴮ-cong; zpow; rot; rot-map; rot-exp; rot-0;
   rot-comp; rot-Σᴮ; scale; scale-map; scale-injective; Respects; coeff;
   coeff-cong; N)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_; amp-≗)
open import PathSum.Hermitian M₀ using (conj-[]ᴬ)
open import PathSum.Ring M₀ using
  (_⊛_; ⊛-cong; ⊛-identityˡ; ⊛-rotˡ; ⊛-rotʳ; conj; conj-cong;
   conj-involutive; conj-rot)
open import PathSum.Ring.Laws M₀ using
  (⊛-comm; ⊛-assoc; ⊛-identityʳ; conj-⊛; Σᴮ-⊛; ⊛-Σᴮ; conj-Σᴮ; scale-⊛ˡ;
   scale-⊛ʳ; conj-scale)

open +-*-Solver using (solve; _:+_; _:-_; :-_; _:=_)

private
  variable
    n k m : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Operators

-- A matrix: the entry from input x to output z.

Mat : ℕ → Set
Mat n = Assign n → Assign n → Amp

-- Its entries read assignments only through their values.

RespectsM : Mat n → Set
RespectsM A = ∀ {x x′ z z′} → (∀ i → x i ≡ x′ i) → (∀ i → z i ≡ z′ i) →
              A x z ≐ A x′ z′

-- An operator: the matrix mat divided by √2^nrm.

record Op (n : ℕ) : Set where
  no-eta-equality
  constructor op
  field
    nrm  : ℕ
    mat  : Mat n
    resp : RespectsM mat

open Op public

-- A row and a column of an operator respect pointwise equality.

respˣ : (U : Op n) (z : Assign n) → Respects (λ w → mat U w z)
respˣ U z g h g≗h = resp U {g} {h} {z} {z} g≗h (λ _ → refl)

respᶻ : (U : Op n) (x : Assign n) → Respects (λ w → mat U x w)
respᶻ U x g h g≗h = resp U {x} {x} {g} {h} (λ _ → refl) g≗h

-- The operator of a path-sum.

⟪_⟫ : PathSum n k m → Op n
⟪_⟫ {k = k} ξ = op k (amp ξ) (λ {x} {x′} {z} {z′} x≗x′ z≗z′ →
  amp-≗ˣ ξ x≗x′ z ∙ amp-≗ ξ x′ z≗z′)


------------------------------------------------------------------------
-- Equality of operators

-- Equal operators: the matrices agree once both normalisations are
-- cleared.  On path-sums this is _≋_ (≋⇒≈, ≈⇒≋).  It is a record, not
-- a definition, so that the two operators can be recovered from the
-- type by unification.

infix 4 _≈_

record _≈_ {n : ℕ} (U V : Op n) : Set where
  constructor ≈-intro
  field
    ≈-at : ∀ x z → scale (nrm V) (mat U x z) ≐ scale (nrm U) (mat V x z)

open _≈_ public

≋⇒≈ : {ξ : PathSum n k m} {k′ m′ : ℕ} {ζ : PathSum n k′ m′} →
      ξ ≋ ζ → ⟪ ξ ⟫ ≈ ⟪ ζ ⟫
≋⇒≈ e = ≈-intro e

≈⇒≋ : {ξ : PathSum n k m} {k′ m′ : ℕ} {ζ : PathSum n k′ m′} →
      ⟪ ξ ⟫ ≈ ⟪ ζ ⟫ → ξ ≋ ζ
≈⇒≋ e = ≈-at e

≈-refl : {U : Op n} → U ≈ U
≈-refl = ≈-intro (λ _ _ _ → refl)

≈-sym : {U V : Op n} → U ≈ V → V ≈ U
≈-sym e = ≈-intro (λ x z i → sym (≈-at e x z i))

-- Transitivity cancels the middle normalisation (scale-injective).

≈-trans : {U V W : Op n} → U ≈ V → V ≈ W → U ≈ W
≈-trans {U = U} {V} {W} e f = ≈-intro (λ x z →
  scale-injective (nrm V) (scale (nrm W) (mat U x z))
                          (scale (nrm U) (mat W x z))
    (scale-comm (nrm V) (nrm W) (mat U x z)
     ∙ scale-map (nrm W) (≈-at e x z)
     ∙ scale-comm (nrm W) (nrm U) (mat V x z)
     ∙ scale-map (nrm U) (≈-at f x z)
     ∙ scale-comm (nrm U) (nrm V) (mat W x z)))

infixr 5 _⟨≈⟩_

_⟨≈⟩_ : {U V W : Op n} → U ≈ V → V ≈ W → U ≈ W
_⟨≈⟩_ = ≈-trans

-- Equal normalisations and equal entries.

≈-by : (U V : Op n) → nrm U ≡ nrm V → (∀ x z → mat U x z ≐ mat V x z) →
       U ≈ V
≈-by U V k≡k′ e = ≈-intro (λ x z →
  scale-exp (mat U x z) (sym k≡k′) ∙ scale-map (nrm U) (e x z))


------------------------------------------------------------------------
-- The product

-- U · V applies V, then U.

infixl 7 _·_

_·_ : Op n → Op n → Op n
U · V = op (nrm U ℕ+ nrm V) (mat U ⊙ mat V)
  (λ {x} {x′} {z} {z′} x≗x′ z≗z′ → Σᴮ-cong (λ w →
    ⊛-cong (resp V {x} {x′} {w} {w} x≗x′ (λ _ → refl))
           (resp U {w} {w} {z} {z′} (λ _ → refl) z≗z′)))

-- Clearing both normalisations of a product clears each factor's.

private
  scale-⊙ : ∀ a b (f g : Assign n → Amp) →
            scale (a ℕ+ b) (Σᴮ (λ w → f w ⊛ g w)) ≐
            Σᴮ (λ w → scale b (f w) ⊛ scale a (g w))
  scale-⊙ a b f g =
    ≐-sym (scale-+ a b (Σᴮ (λ w → f w ⊛ g w)))
    ∙ scale-map a (scale-Σᴮ b (λ w → f w ⊛ g w))
    ∙ scale-Σᴮ a (λ w → scale b (f w ⊛ g w))
    ∙ Σᴮ-cong (λ w →
        scale-map a (≐-sym (scale-⊛ˡ b (f w) (g w)))
        ∙ ≐-sym (scale-⊛ʳ a (scale b (f w)) (g w)))

·-cong : {U U′ V V′ : Op n} → U ≈ U′ → V ≈ V′ → U · V ≈ U′ · V′
·-cong {U = U} {U′} {V} {V′} eU eV = ≈-intro (λ x z →
  scale-⊙ (nrm U′) (nrm V′) (λ w → mat V x w) (λ w → mat U w z)
  ∙ Σᴮ-cong (λ w → ⊛-cong (≈-at eV x w) (≈-at eU w z))
  ∙ ≐-sym (scale-⊙ (nrm U) (nrm V) (λ w → mat V′ x w) (λ w → mat U′ w z)))

·-congˡ : {U U′ : Op n} (V : Op n) → U ≈ U′ → U · V ≈ U′ · V
·-congˡ V e = ·-cong e (≈-refl {U = V})

·-congʳ : (U : Op n) {V V′ : Op n} → V ≈ V′ → U · V ≈ U · V′
·-congʳ U e = ·-cong (≈-refl {U = U}) e

-- Associativity: the two double sums, exchanged.

·-assoc : (U V W : Op n) → (U · V) · W ≈ U · (V · W)
·-assoc U V W = ≈-by ((U · V) · W) (U · (V · W))
  (ℕ.+-assoc (nrm U) (nrm V) (nrm W))
  (λ x z →
     ⊛-Σᴮ-each x z
     ∙ Σᴮ-swap (λ w v → (mat W x w ⊛ mat V w v) ⊛ mat U v z)
     ∙ Σᴮ-cong (λ v → ≐-sym (Σᴮ-⊛ (λ w → mat W x w ⊛ mat V w v)
                                   (mat U v z))))
  where
  ⊛-Σᴮ-each : ∀ x z →
    Σᴮ (λ w → mat W x w ⊛ Σᴮ (λ v → mat V w v ⊛ mat U v z)) ≐
    Σᴮ (λ w → Σᴮ (λ v → (mat W x w ⊛ mat V w v) ⊛ mat U v z))
  ⊛-Σᴮ-each x z = Σᴮ-cong (λ w →
    ⊛-Σᴮ (mat W x w) (λ v → mat V w v ⊛ mat U v z)
    ∙ Σᴮ-cong (λ v → ≐-sym (⊛-assoc (mat W x w) (mat V w v) (mat U v z))))


------------------------------------------------------------------------
-- The identity

private
  =ᵇ-sym : ∀ a b → (a =ᵇ b) ≡ (b =ᵇ a)
  =ᵇ-sym true  true  = refl
  =ᵇ-sym true  false = refl
  =ᵇ-sym false true  = refl
  =ᵇ-sym false false = refl

same-sym : (x z : Assign n) → same x z ≡ same z x
same-sym {ℕ.zero}  x z = refl
same-sym {ℕ.suc n} x z = cong₂ _∧_ (=ᵇ-sym (x zero) (z zero))
  (same-sym (λ j → x (suc j)) (λ j → z (suc j)))

I : Op n
I = op 0 δ (λ {x} {x′} {z} {z′} x≗x′ z≗z′ i →
  cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-≗ x≗x′ z≗z′))

-- I · U sums U's column against δ on the right, U · I on the left.

·-identityˡ : (U : Op n) → I · U ≈ U
·-identityˡ U = ≈-by (I · U) U refl (λ x z →
  Σᴮ-cong (λ w →
    ⊛-cong {a = mat U x w} ≐-refl
           (if-cong {p = same w z} {q = same z w} (same-sym w z) ≐-refl)
    ∙ ⊛-if (same z w) (mat U x w) (zpow 0ℤ))
  ∙ Σᴮ-δ z (λ w → mat U x w ⊛ zpow 0ℤ)
         (λ g h g≗h → ⊛-cong (respᶻ U x g h g≗h) ≐-refl)
  ∙ ⊛-identityʳ (mat U x z))

·-identityʳ : (U : Op n) → U · I ≈ U
·-identityʳ U = ≈-by (U · I) U (ℕ.+-identityʳ (nrm U)) (λ x z →
  Σᴮ-cong (λ w → if-⊛ (same x w) (zpow 0ℤ) (mat U w z))
  ∙ Σᴮ-δ x (λ w → zpow 0ℤ ⊛ mat U w z)
         (λ g h g≗h → ⊛-cong ≐-refl (respˣ U z g h g≗h))
  ∙ ⊛-identityˡ (mat U x z))


------------------------------------------------------------------------
-- The adjoint

infix 8 _†

_† : Op n → Op n
U † = op (nrm U) (λ x z → conj (mat U z x))
  (λ {x} {x′} {z} {z′} x≗x′ z≗z′ →
     conj-cong {mat U z x} {mat U z′ x′} (resp U z≗z′ x≗x′))

†-cong : {U V : Op n} → U ≈ V → U † ≈ V †
†-cong {U = U} {V} e = ≈-intro (λ x z →
  ≐-sym (conj-scale (nrm V) (mat U z x))
  ∙ conj-cong (≈-at e z x)
  ∙ conj-scale (nrm U) (mat V z x))

†-involutive : (U : Op n) → U † † ≈ U
†-involutive U = ≈-by (U † †) U refl (λ x z → conj-involutive (mat U x z))

-- (UV)† = V†U†.

†-· : (U V : Op n) → (U · V) † ≈ V † · U †
†-· U V = ≈-by ((U · V) †) (V † · U †) (ℕ.+-comm (nrm U) (nrm V)) (λ x z →
  conj-Σᴮ (λ w → mat V z w ⊛ mat U w x)
  ∙ Σᴮ-cong (λ w → conj-⊛ (mat V z w) (mat U w x)
                   ∙ ⊛-comm (conj (mat V z w)) (conj (mat U w x))))

†-I : I {n} † ≈ I
†-I = ≈-by (I †) I refl (λ x z →
  conj-[]ᴬ (same z x)
  ∙ if-cong {p = same z x} {q = same x z} (same-sym z x) ≐-refl)


------------------------------------------------------------------------
-- Global phases

-- ζ^e U.

infixr 8 _◃_

_◃_ : ℤ → Op n → Op n
e ◃ U = op (nrm U) (λ x z → rot e (mat U x z))
  (λ {x} {x′} {z} {z′} x≗x′ z≗z′ →
     rot-map {mat U x z} {mat U x′ z′} e (resp U x≗x′ z≗z′))

◃-cong : (e : ℤ) {U V : Op n} → U ≈ V → e ◃ U ≈ e ◃ V
◃-cong e {U} {V} eq = ≈-intro (λ x z →
  scale-rot (nrm V) e (mat U x z)
  ∙ rot-map e (≈-at eq x z)
  ∙ ≐-sym (scale-rot (nrm U) e (mat V x z)))

◃-0 : (U : Op n) → 0ℤ ◃ U ≈ U
◃-0 U = ≈-by (0ℤ ◃ U) U refl (λ x z → rot-0 (mat U x z))

◃-◃ : (e e′ : ℤ) (U : Op n) → e ◃ e′ ◃ U ≈ (e + e′) ◃ U
◃-◃ e e′ U = ≈-by (e ◃ e′ ◃ U) ((e + e′) ◃ U) refl
  (λ x z → rot-comp e e′ (mat U x z))

◃-exp : {e e′ : ℤ} (U : Op n) → e ≡ e′ → e ◃ U ≈ e′ ◃ U
◃-exp {e = e} {e′} U eq = ≈-by (e ◃ U) (e′ ◃ U) refl
  (λ x z → rot-exp {e} {e′} (mat U x z) eq)

-- A rotation depends on its exponent modulo N, the order of ζ.

rot-mod : ∀ {e e′} a → (+ N) ∣ (e - e′) → rot e a ≐ rot e′ a
rot-mod {e} {e′} a d i = coeff-cong a ((+ toℕ i) - e) ((+ toℕ i) - e′)
  (subst ((+ N) ∣_) (shape e e′ (+ toℕ i)) (∣m⇒∣-m d))
  where
  shape : ∀ u v t → - (u - v) ≡ (t - u) - (t - v)
  shape = solve 3 (λ u v t → :- (u :- v) := (t :- u) :- (t :- v)) refl

◃-mod : {e e′ : ℤ} (U : Op n) → (+ N) ∣ (e - e′) → e ◃ U ≈ e′ ◃ U
◃-mod {e = e} {e′} U d = ≈-by (e ◃ U) (e′ ◃ U) refl
  (λ x z → rot-mod {e} {e′} (mat U x z) d)

-- Phases move through products and adjoints.

◃-·ˡ : (e : ℤ) (U V : Op n) → (e ◃ U) · V ≈ e ◃ (U · V)
◃-·ˡ e U V = ≈-by ((e ◃ U) · V) (e ◃ (U · V)) refl (λ x z →
  Σᴮ-cong (λ w → ⊛-rotʳ e (mat V x w) (mat U w z))
  ∙ ≐-sym (rot-Σᴮ e (λ w → mat V x w ⊛ mat U w z)))

◃-·ʳ : (e : ℤ) (U V : Op n) → U · (e ◃ V) ≈ e ◃ (U · V)
◃-·ʳ e U V = ≈-by (U · (e ◃ V)) (e ◃ (U · V)) refl (λ x z →
  Σᴮ-cong (λ w → ⊛-rotˡ e (mat V x w) (mat U w z))
  ∙ ≐-sym (rot-Σᴮ e (λ w → mat V x w ⊛ mat U w z)))

◃-† : (e : ℤ) (U : Op n) → (e ◃ U) † ≈ (- e) ◃ (U †)
◃-† e U = ≈-by ((e ◃ U) †) ((- e) ◃ (U †)) refl
  (λ x z → conj-rot e (mat U z x))


------------------------------------------------------------------------
-- Rebracketing

-- The shapes the hierarchy uses: a conjugate U P U†, and a product of
-- three moved into a product of two.

·-assoc₃ : (A B C D : Op n) → A · B · C · D ≈ A · (B · C) · D
·-assoc₃ A B C D = ·-congˡ D (·-assoc A B C)


------------------------------------------------------------------------
-- Unitaries

Unitary : Op n → Set
Unitary U = (U † · U ≈ I) × (U · U † ≈ I)

Unitary-cong : {U V : Op n} → U ≈ V → Unitary U → Unitary V
Unitary-cong {U = U} {V} e (l , r) =
  ≈-sym (·-cong (†-cong e) e) ⟨≈⟩ l ,
  ≈-sym (·-cong e (†-cong e)) ⟨≈⟩ r

Unitary-I : Unitary (I {n})
Unitary-I = ·-identityʳ (I †) ⟨≈⟩ †-I , ·-identityˡ (I †) ⟨≈⟩ †-I

Unitary-† : (U : Op n) → Unitary U → Unitary (U †)
Unitary-† U (l , r) = ·-congˡ (U †) (†-involutive U) ⟨≈⟩ r ,
                      ·-congʳ (U †) (†-involutive U) ⟨≈⟩ l

-- Cancelling a unitary next to its adjoint.

cancelˡ : (U V : Op n) → Unitary U → U † · (U · V) ≈ V
cancelˡ U V (l , _) =
  ≈-sym (·-assoc (U †) U V) ⟨≈⟩ ·-congˡ V l ⟨≈⟩ ·-identityˡ V

cancelˡ′ : (U V : Op n) → Unitary U → U · (U † · V) ≈ V
cancelˡ′ U V (_ , r) =
  ≈-sym (·-assoc U (U †) V) ⟨≈⟩ ·-congˡ V r ⟨≈⟩ ·-identityˡ V

cancelʳ : (U V : Op n) → Unitary U → V · U · U † ≈ V
cancelʳ U V (_ , r) =
  ·-assoc V U (U †) ⟨≈⟩ ·-congʳ V r ⟨≈⟩ ·-identityʳ V

cancelʳ′ : (U V : Op n) → Unitary U → V · U † · U ≈ V
cancelʳ′ U V (l , _) =
  ·-assoc V (U †) U ⟨≈⟩ ·-congʳ V l ⟨≈⟩ ·-identityʳ V

Unitary-· : (U V : Op n) → Unitary U → Unitary V → Unitary (U · V)
Unitary-· U V uU uV =
  (·-congˡ (U · V) (†-· U V)
   ⟨≈⟩ ·-assoc (V †) (U †) (U · V)
   ⟨≈⟩ ·-congʳ (V †) (cancelˡ U V uU)
   ⟨≈⟩ proj₁ uV) ,
  (·-congʳ (U · V) (†-· U V)
   ⟨≈⟩ ·-assoc U V (V † · U †)
   ⟨≈⟩ ·-congʳ U (cancelˡ′ V (U †) uV)
   ⟨≈⟩ proj₂ uU)

Unitary-◃ : (e : ℤ) (U : Op n) → Unitary U → Unitary (e ◃ U)
Unitary-◃ e U (l , r) =
  (·-congˡ (e ◃ U) (◃-† e U)
   ⟨≈⟩ ◃-·ˡ (- e) (U †) (e ◃ U)
   ⟨≈⟩ ◃-cong (- e) (◃-·ʳ e (U †) U)
   ⟨≈⟩ ◃-◃ (- e) e (U † · U)
   ⟨≈⟩ ◃-exp (U † · U) (+-inverseˡ e)
   ⟨≈⟩ ◃-0 (U † · U)
   ⟨≈⟩ l) ,
  (·-congʳ (e ◃ U) (◃-† e U)
   ⟨≈⟩ ◃-·ʳ (- e) (e ◃ U) (U †)
   ⟨≈⟩ ◃-cong (- e) (◃-·ˡ e U (U †))
   ⟨≈⟩ ◃-◃ (- e) e (U · U †)
   ⟨≈⟩ ◃-exp (U · U †) (+-inverseˡ e)
   ⟨≈⟩ ◃-0 (U · U †)
   ⟨≈⟩ r)
