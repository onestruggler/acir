------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H , S , CZ} are isometries (Amy, QPL 2018,
-- definition 2.4 and proposition 2.10)
--
-- Proposition 2.10 identifies the operator of ⟦ C ⟧ with the matrix of
-- the circuit, which PathSum.CircuitSemantics builds a column at a
-- time: the column of ⟦ C ⟧ at the input x is the gates of C applied
-- in turn to the basis column δ x (prop-2-10).  Each gate acts on
-- columns by its own unnormalised matrix, and this module shows that
-- each of those matrices is a multiple of an isometry: it multiplies
-- the Hermitian product of any two columns (PathSum.Hermitian's inner)
-- by a constant.
--
--   * S and CZ multiply the entry at z by a power of ζ read off z, the
--     same power in both columns, and a common phase cancels from a
--     product a · conj b (inner-S, inner-CZ).
--   * A Hadamard on w pairs the assignments z[w≔0] and z[w≔1].  It
--     turns the entries a , b of one column there into a + b and
--     a - b, and those c , d of the other into c + d and c - d, and the
--     polarised parallelogram law adds the products of the new entries
--     up to twice a · conj c + b · conj d (inner-H).  So a Hadamard
--     doubles the product.
--
-- A circuit therefore multiplies the product of two columns by 2^k,
-- k = norm C the number of its Hadamards (inner-apply); the basis
-- columns are orthonormal (inner-δ); and so the columns of ⟦ C ⟧ are
-- orthogonal, each of norm 2^k (circuit-isometry):
--
--   Σ_z amp ⟦ C ⟧ x z · conj (amp ⟦ C ⟧ x′ z) = 2^k [x = x′],
--
-- which is U†U = I for U the operator of ⟦ C ⟧, its entries being
-- amp ⟦ C ⟧ x z / √2^k and √2 real.  That is PathSum.PartialIsometry's
-- Isometric (circuit-Isometric), so ⟦ C ⟧ is well-formed in the sense
-- of definition 2.4 as a theorem (circuit-PartialIsometric), and
-- lemma 4.1 applies to it under the paper's own hypothesis.
--
-- What is proved is that U is an isometry, U†U = I.  That it is
-- unitary, UU† = I as well, follows for a square matrix by linear
-- algebra that is not formalised here, and is not stated.
--
-- The lemma for a Hadamard, and hence the one for a circuit, asks both
-- columns to respect pointwise equality of assignments, since the
-- pairing of z[w≔0] with z[w≔1] meets assignments only pointwise equal
-- to those the sum visits; the basis columns do.  The helpers below
-- that carry that respect through the gates, and read off the sign of
-- a Hadamard, are private to PathSum.CircuitSemantics and are
-- re-proved here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _^_)

module PathSum.Unitarity (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; *-identityˡ; *-identityʳ; *-zeroʳ; *-comm; pos-*)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-≔; ≔-cong; same)
open import PathSum.Circuit M using (Gate; H; S; CZ; Circuit; norm; ⟦_⟧)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; gateᴬ; applyᴬ; prop-2-10)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _-ᴬ_; _·ᴬ_; _≐_; rot; rot-map; rot-exp; rot-0;
   rot-anti; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Hermitian M₀ using
  (Σᵃ; Σᵃ-cong; Σᵃ-·ᴬ; Σᵃ-at; [_]ᴬ; []ᴬ-resp; inner; inner-cong;
   inner-phase; inner-basis)
open import PathSum.PartialIsometry M₀ using
  (Isometric; PartialIsometric; Isometric⇒PartialIsometric)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Ring M₀ using
  (_⊛_; conj; ⊛-cong; conj-cong; ·ᴬ-cong; ·ᴬ-·ᴬ; ⊛-conj-parallelogram)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The gates, entry by entry

-- As in PathSum.CircuitSemantics, where these are private: a rotation
-- is compared only with a rotation by the same exponent, exponents
-- being changed by rot-exp alone.

private
  rot-cong : (a a′ : Amp) (e e′ : ℤ) → e ≡ e′ → a ≐ a′ →
             rot e a ≐ rot e′ a′
  rot-cong a a′ e e′ ee aa i =
    trans (rot-map e aa i) (rot-exp {e} {e′} a′ ee i)

  sum-cong : (a a′ b b′ : Amp) (e e′ : ℤ) → a ≐ a′ → e ≡ e′ → b ≐ b′ →
             (a +ᴬ rot e b) ≐ (a′ +ᴬ rot e′ b′)
  sum-cong a a′ b b′ e e′ aa ee bb i =
    cong₂ _+_ (aa i) (rot-cong b b′ e e′ ee bb i)

  -- The sign of a Hadamard: ζ^0 = 1 where its wire is 0, and
  -- ζ^rank = -1 where it is 1.

  sign-0 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ → b ≐ b′ →
           (a +ᴬ rot e b) ≐ (a′ +ᴬ b′)
  sign-0 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ} b ee i) (trans (rot-0 b i) (bb i)))

  sign-1 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ + (+ rank) →
           b ≐ b′ → (a +ᴬ rot e b) ≐ (a′ -ᴬ b′)
  sign-1 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ + (+ rank)} b ee i)
      (trans (rot-anti 0ℤ b i) (cong -_ (trans (rot-0 b i) (bb i)))))

  -- The gates act entry by entry, so they preserve respect for
  -- pointwise equality of assignments.

  gateᴬ-resp : (g : Gate n) {ψ : Column n} → Respects ψ →
               Respects (gateᴬ g ψ)
  gateᴬ-resp (H w) {ψ} resp z z′ zz =
    sum-cong (ψ (z [ w ≔ false ])) (ψ (z′ [ w ≔ false ]))
             (ψ (z [ w ≔ true ])) (ψ (z′ [ w ≔ true ]))
             (½ * [ z w ]ᶻ) (½ * [ z′ w ]ᶻ)
             (resp (z [ w ≔ false ]) (z′ [ w ≔ false ])
                   (≔-cong w false zz))
             (cong (λ b → ½ * [ b ]ᶻ) (zz w))
             (resp (z [ w ≔ true ]) (z′ [ w ≔ true ]) (≔-cong w true zz))
  gateᴬ-resp (S w) {ψ} resp z z′ zz =
    rot-cong (ψ z) (ψ z′) (¼ * [ z w ]ᶻ) (¼ * [ z′ w ]ᶻ)
             (cong (λ b → ¼ * [ b ]ᶻ) (zz w)) (resp z z′ zz)
  gateᴬ-resp (CZ w v) {ψ} resp z z′ zz =
    rot-cong (ψ z) (ψ z′) (½ * [ z w ∧ z v ]ᶻ) (½ * [ z′ w ∧ z′ v ]ᶻ)
             (cong₂ (λ a b → ½ * [ a ∧ b ]ᶻ) (zz w) (zz v))
             (resp z z′ zz)


------------------------------------------------------------------------
-- Each gate is a multiple of an isometry

-- S and CZ are diagonal phases, and a common phase cancels.

inner-S : (w : Fin n) (ψ φ : Column n) →
          inner (gateᴬ (S w) ψ) (gateᴬ (S w) φ) ≐ inner ψ φ
inner-S w ψ φ = inner-phase (λ z → ¼ * [ z w ]ᶻ) ψ φ

inner-CZ : (w v : Fin n) (ψ φ : Column n) →
           inner (gateᴬ (CZ w v) ψ) (gateᴬ (CZ w v) φ) ≐ inner ψ φ
inner-CZ w v ψ φ = inner-phase (λ z → ½ * [ z w ∧ z v ]ᶻ) ψ φ

-- A Hadamard on w doubles the product.  The sum over z is taken a pair
-- z[w≔0] , z[w≔1] at a time, on both sides; the new entries at the
-- pair are a + b , a - b and c + d , c - d, and the polarised
-- parallelogram law makes their products twice a · c̄ + b · d̄.

inner-H : (w : Fin n) {ψ φ : Column n} → Respects ψ → Respects φ →
          inner (gateᴬ (H w) ψ) (gateᴬ (H w) φ) ≐ (+ 2) ·ᴬ inner ψ φ
inner-H {n} w {ψ} {φ} rψ rφ i =
  trans (Σᵃ-at w F respF i)
    (trans (Σᵃ-cong (λ z → masked (z w) (pair z)) i)
      (trans (Σᵃ-·ᴬ (+ 2) P i)
             (cong (λ t → (+ 2) * t) (sym (Σᵃ-at w G respG i)))))
  where
  F G : Assign n → Amp
  F z = gateᴬ (H w) ψ z ⊛ conj (gateᴬ (H w) φ z)
  G z = ψ z ⊛ conj (φ z)

  -- The pairs of the old column products.

  P : Assign n → Amp
  P z = if z w then 0ᴬ else (G (z [ w ≔ false ]) +ᴬ G (z [ w ≔ true ]))

  respF : Respects F
  respF g h gh = ⊛-cong (gateᴬ-resp (H w) rψ g h gh)
                        (conj-cong (gateᴬ-resp (H w) rφ g h gh))

  respG : Respects G
  respG g h gh = ⊛-cong (rψ g h gh) (conj-cong (rφ g h gh))

  masked : ∀ b {A B : Amp} → A ≐ (+ 2) ·ᴬ B →
           (if b then 0ᴬ else A) ≐ (+ 2) ·ᴬ (if b then 0ᴬ else B)
  masked true  _ _ = sym (*-zeroʳ (+ 2))
  masked false p   = p

  e₀ : ∀ z → ½ * [ (z [ w ≔ false ]) w ]ᶻ ≡ 0ℤ
  e₀ z =
    trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w false)) (*-zeroʳ ½)

  e₁ : ∀ z → ½ * [ (z [ w ≔ true ]) w ]ᶻ ≡ 0ℤ + (+ rank)
  e₁ z = trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w true))
               (trans (*-identityʳ ½) (sym (+-identityˡ ½)))

  -- The new entries of a column at the pair.

  at-0 : (χ : Column n) → Respects χ → ∀ z →
         gateᴬ (H w) χ (z [ w ≔ false ]) ≐
         χ (z [ w ≔ false ]) +ᴬ χ (z [ w ≔ true ])
  at-0 χ rχ z =
    sign-0 (χ (z [ w ≔ false ] [ w ≔ false ])) (χ (z [ w ≔ false ]))
           (χ (z [ w ≔ false ] [ w ≔ true ])) (χ (z [ w ≔ true ]))
           (½ * [ (z [ w ≔ false ]) w ]ᶻ)
           (rχ _ _ (≔-≔ z w false false)) (e₀ z)
           (rχ _ _ (≔-≔ z w false true))

  at-1 : (χ : Column n) → Respects χ → ∀ z →
         gateᴬ (H w) χ (z [ w ≔ true ]) ≐
         χ (z [ w ≔ false ]) -ᴬ χ (z [ w ≔ true ])
  at-1 χ rχ z =
    sign-1 (χ (z [ w ≔ true ] [ w ≔ false ])) (χ (z [ w ≔ false ]))
           (χ (z [ w ≔ true ] [ w ≔ true ])) (χ (z [ w ≔ true ]))
           (½ * [ (z [ w ≔ true ]) w ]ᶻ)
           (rχ _ _ (≔-≔ z w true false)) (e₁ z)
           (rχ _ _ (≔-≔ z w true true))

  pair : ∀ z → F (z [ w ≔ false ]) +ᴬ F (z [ w ≔ true ]) ≐
               (+ 2) ·ᴬ (G (z [ w ≔ false ]) +ᴬ G (z [ w ≔ true ]))
  pair z j = trans
    (cong₂ _+_ (⊛-cong (at-0 ψ rψ z) (conj-cong (at-0 φ rφ z)) j)
               (⊛-cong (at-1 ψ rψ z) (conj-cong (at-1 φ rφ z)) j))
    (⊛-conj-parallelogram (ψ (z [ w ≔ false ])) (ψ (z [ w ≔ true ]))
                          (φ (z [ w ≔ false ])) (φ (z [ w ≔ true ])) j)


------------------------------------------------------------------------
-- Circuits

-- A circuit multiplies the product of two columns by 2^k, k the number
-- of its Hadamards.

inner-apply : (C : Circuit n) {ψ φ : Column n} → Respects ψ →
              Respects φ →
              inner (applyᴬ C ψ) (applyᴬ C φ) ≐
              (+ (2 ^ norm C)) ·ᴬ inner ψ φ
inner-apply []           {ψ} {φ} rψ rφ i = sym (*-identityˡ (inner ψ φ i))
inner-apply (H w ∷ C)    {ψ} {φ} rψ rφ i =
  trans (inner-apply C {gateᴬ (H w) ψ} {gateᴬ (H w) φ}
                     (gateᴬ-resp (H w) rψ) (gateᴬ-resp (H w) rφ) i)
    (trans (·ᴬ-cong (+ (2 ^ norm C)) (inner-H w rψ rφ) i)
      (trans (·ᴬ-·ᴬ (+ (2 ^ norm C)) (+ 2) (inner ψ φ) i)
             (cong (λ t → t * inner ψ φ i) (twice (norm C)))))
  where
  twice : ∀ k → + (2 ^ k) * (+ 2) ≡ + (2 ^ suc k)
  twice k = trans (*-comm (+ (2 ^ k)) (+ 2)) (sym (pos-* 2 (2 ^ k)))
inner-apply (S w ∷ C)    {ψ} {φ} rψ rφ i =
  trans (inner-apply C {gateᴬ (S w) ψ} {gateᴬ (S w) φ}
                     (gateᴬ-resp (S w) rψ) (gateᴬ-resp (S w) rφ) i)
        (·ᴬ-cong (+ (2 ^ norm C)) (inner-S w ψ φ) i)
inner-apply (CZ w v ∷ C) {ψ} {φ} rψ rφ i =
  trans (inner-apply C {gateᴬ (CZ w v) ψ} {gateᴬ (CZ w v) φ}
                     (gateᴬ-resp (CZ w v) rψ) (gateᴬ-resp (CZ w v) rφ) i)
        (·ᴬ-cong (+ (2 ^ norm C)) (inner-CZ w v ψ φ) i)

-- The basis columns are orthonormal: δ x is z ↦ [ same x z ]ᴬ.

inner-δ : (x x′ : Assign n) → inner (δ x) (δ x′) ≐ [ same x x′ ]ᴬ
inner-δ x x′ = inner-basis x x′

-- U†U = I: the columns of ⟦ C ⟧ are orthogonal, each of norm 2^k,
-- which the normalisation 1/√2^k makes 1.

circuit-isometry : (C : Circuit n) (x x′ : Assign n) →
                   Σᵃ (λ z → amp ⟦ C ⟧ x z ⊛ conj (amp ⟦ C ⟧ x′ z)) ≐
                   (+ (2 ^ norm C)) ·ᴬ [ same x x′ ]ᴬ
circuit-isometry C x x′ i =
  trans (inner-cong {ψ = amp ⟦ C ⟧ x} {ψ′ = applyᴬ C (δ x)}
                    {φ = amp ⟦ C ⟧ x′} {φ′ = applyᴬ C (δ x′)}
                    (prop-2-10 C x) (prop-2-10 C x′) i)
    (trans (inner-apply C {δ x} {δ x′} ([]ᴬ-resp x) ([]ᴬ-resp x′) i)
           (·ᴬ-cong (+ (2 ^ norm C)) (inner-δ x x′) i))

-- So ⟦ C ⟧ satisfies definition 2.4: its operator is an isometry, and
-- a fortiori a partial isometry.

circuit-Isometric : (C : Circuit n) → Isometric ⟦ C ⟧
circuit-Isometric C = circuit-isometry C

circuit-PartialIsometric : (C : Circuit n) → PartialIsometric ⟦ C ⟧
circuit-PartialIsometric C =
  Isometric⇒PartialIsometric ⟦ C ⟧ (circuit-Isometric C)
