------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H, X, CNOT, R_k, R_k†} are well formed, so section
-- 4.1's restriction applies to them (Amy, QPL 2018, sections 2.2 and
-- 4.1)
--
-- Lemma 4.1 -- a well-formed path-sum is the identity exactly when its
-- isometry restriction is -- needs well-formedness, and
-- PathSum.CRK.Semantics proves it for circuits over {H, CNOT, R_k,
-- R_k†} by showing that every column of ⟦ C ⟧ has trace-form norm
-- 2^(norm C).  PathSum.CRK.WithX adds the gate X, read as
-- |x⟩ ↦ |1 ⊕ x⟩ (the section-4 identity is drawn with it), but stops at
-- proposition 2.10; this module carries the norm argument over.  X
-- moves the entry at z with the bit on its wire negated to z, so it
-- pairs the assignments z[w≔0] and z[w≔1] and swaps each pair
-- (colN-X); the other gates are PathSum.CRK.Semantics's, whose norm
-- lemmas are private there and re-proved here as they are.  So every
-- column of ⟦ C ⟧ has norm 2^(norm C) (⟦⟧-unit-columns) and ⟦ C ⟧ is
-- WellFormed (circuit-WellFormed).
--
-- With that, the isometry restriction is available for these circuits
-- in both forms.  An interpretation state of PathSum.CRK.WithX holds
-- affine forms c ⊕ S on its wires, which are exactly the forms
-- PathSum.Gauss eliminates over -- its pivots and its verdict already
-- read the constant -- so Gaussian elimination reifies or refutes the
-- restriction of every such circuit (reification-WithX): an X gate
-- after the last Hadamard on a wire makes that wire's output
-- 1 ⊕ y, and the step substitutes y ← ¬x.  What was missing for section
-- 4's {H, X, CNOT, T} circuits was well-formedness, not the
-- elimination.  The restriction of PathSum.Restrict, for arbitrary
-- outputs, applies as well; PathSum.Examples.Restrict runs both on
-- small closed circuits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _^_; _∸_)

module PathSum.CRK.WithX.WellFormed (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-zeroʳ;
   *-assoc; *-comm; pos-*; ≤-reflexive)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-cong; same; same-refl; same-≗)
open import PathSum.AssignSum using
  (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-*; Σᶻ-0; Σᶻ-point; Σᶻ-at)
open import PathSum.Base using (PathSum; out; phase; idPS; Internal)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.CRK.Amp M₀ using (toPS)
open import PathSum.CRK.WithX M₀ using
  (Gate; H; X; CNOT; R; R†; Circuit; norm; run; ⟦_⟧; gateᴬ; applyᴬ;
   gateᴬ-resp; prop-2-10)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _-ᴬ_; _≐_; zpow; rot; rot-exp; rot-0; rot-anti;
   Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.Gauss M₀ using (Reification; reification)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Norm M₀ using
  (‖_‖²; ‖‖²-cong; ‖‖²-rot; parallelogram; ‖zpow0‖²; ‖0ᴬ‖²)
open import PathSum.Order M using (pow; Ord≤)
open import PathSum.Polynomial using (x[_]; μ)
open import PathSum.Reduction M using (½)

import PathSum.CRK.Circuit

private
  module KC = PathSum.CRK.Circuit M

  variable
    n m : ℕ


------------------------------------------------------------------------
-- The norm of a column

colN : Column n → ℤ
colN ψ = Σᶻ (λ z → ‖ ψ z ‖²)

private
  -- The two terms of a Hadamard, with the sign its wire gives
  -- (PathSum.CRK.Semantics has these privately).

  sign-0 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ → b ≐ b′ →
           (a +ᴬ rot e b) ≐ (a′ +ᴬ b′)
  sign-0 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ} b ee i) (trans (rot-0 b i) (bb i)))

  sign-1 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ + (+ rank) →
           b ≐ b′ → (a +ᴬ rot e b) ≐ (a′ -ᴬ b′)
  sign-1 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ + (+ rank)} b ee i)
      (trans (rot-anti 0ℤ b i) (cong -_ (trans (rot-0 b i) (bb i)))))

  δ-resp : (x : Assign n) → Respects (δ x)
  δ-resp x z z′ zz i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x} {z = z} {z′ = z′} (λ _ → refl) zz)


------------------------------------------------------------------------
-- Each gate multiplies the norm of a column by 1 or, a Hadamard, by 2

-- X swaps the entries at z[w≔0] and z[w≔1].

colN-X : (w : Fin n) (ψ : Column n) → Respects ψ →
         colN (gateᴬ (X w) ψ) ≡ colN ψ
colN-X {n} w ψ resp =
  trans (Σᶻ-at w F respF)
    (trans (Σᶻ-cong (λ z → cong (λ s → if z w then 0ℤ else s) (pair z)))
           (sym (Σᶻ-at w G respG)))
  where
  F G : Assign n → ℤ
  F z = ‖ gateᴬ (X w) ψ z ‖²
  G z = ‖ ψ z ‖²

  respF : RespectsZ F
  respF z z′ zz = ‖‖²-cong (gateᴬ-resp (X w) resp z z′ zz)

  respG : RespectsZ G
  respG z z′ zz = ‖‖²-cong (resp z z′ zz)

  at : ∀ z b → F (z [ w ≔ b ]) ≡ G (z [ w ≔ not b ])
  at z b = ‖‖²-cong (resp _ _ (λ j →
    trans (cong (λ u → ((z [ w ≔ b ]) [ w ≔ u ]) j)
                (cong not (≔-here z w b)))
          (≔-≔ z w b (not b) j)))

  pair : ∀ z → F (z [ w ≔ false ]) + F (z [ w ≔ true ]) ≡
               G (z [ w ≔ false ]) + G (z [ w ≔ true ])
  pair z = trans (cong₂ _+_ (at z false) (at z true))
                 (+-comm (G (z [ w ≔ true ])) (G (z [ w ≔ false ])))

-- Phase gates multiply every entry by a power of ζ.

colN-R : (k : ℕ) (w : Fin n) (ψ : Column n) →
         colN (gateᴬ (R k w) ψ) ≡ colN ψ
colN-R k w ψ = Σᶻ-cong (λ z → trans
  (‖‖²-cong {gateᴬ (R k w) ψ z} {rot (pow (M ∸ k) * [ z w ]ᶻ) (ψ z)}
            (λ _ → refl))
  (‖‖²-rot (pow (M ∸ k) * [ z w ]ᶻ) (ψ z)))

colN-R† : (k : ℕ) (w : Fin n) (ψ : Column n) →
          colN (gateᴬ (R† k w) ψ) ≡ colN ψ
colN-R† k w ψ = Σᶻ-cong (λ z → trans
  (‖‖²-cong {gateᴬ (R† k w) ψ z} {rot (- (pow (M ∸ k) * [ z w ]ᶻ)) (ψ z)}
            (λ _ → refl))
  (‖‖²-rot (- (pow (M ∸ k) * [ z w ]ᶻ)) (ψ z)))

-- CNOT pairs the assignments z[t≔0] and z[t≔1], swapped when the
-- control reads 1.

colN-CNOT : (c t : Fin n) (p : c ≢ t) (ψ : Column n) → Respects ψ →
            colN (gateᴬ (CNOT c t p) ψ) ≡ colN ψ
colN-CNOT {n} c t p ψ resp =
  trans (Σᶻ-at t F respF)
    (trans (Σᶻ-cong (λ z → cong (λ s → if z t then 0ℤ else s) (pair z)))
           (sym (Σᶻ-at t G respG)))
  where
  F G : Assign n → ℤ
  F z = ‖ gateᴬ (CNOT c t p) ψ z ‖²
  G z = ‖ ψ z ‖²

  respF : RespectsZ F
  respF z z′ zz = ‖‖²-cong (gateᴬ-resp (CNOT c t p) resp z z′ zz)

  respG : RespectsZ G
  respG z z′ zz = ‖‖²-cong (resp z z′ zz)

  at : ∀ z b → F (z [ t ≔ b ]) ≡ G (z [ t ≔ b xor z c ])
  at z b = ‖‖²-cong (resp _ _ (λ j →
    trans (≔-≔ z t b ((z [ t ≔ b ]) t xor (z [ t ≔ b ]) c) j)
          (cong (λ u → (z [ t ≔ u ]) j)
                (cong₂ _xor_ (≔-here z t b) (≔-there z b p)))))

  swap : ∀ z (b : Bool) →
         G (z [ t ≔ b ]) + G (z [ t ≔ not b ]) ≡
         G (z [ t ≔ false ]) + G (z [ t ≔ true ])
  swap z false = refl
  swap z true  = +-comm (G (z [ t ≔ true ])) (G (z [ t ≔ false ]))

  pair : ∀ z → F (z [ t ≔ false ]) + F (z [ t ≔ true ]) ≡
               G (z [ t ≔ false ]) + G (z [ t ≔ true ])
  pair z = trans (cong₂ _+_ (at z false) (at z true)) (swap z (z c))

-- A Hadamard: the parallelogram law on each pair doubles the norm.

private
  pair-norm : (X₀ X₁ a b : Amp) → X₀ ≐ (a +ᴬ b) → X₁ ≐ (a -ᴬ b) →
              ‖ X₀ ‖² + ‖ X₁ ‖² ≡ (+ 2) * (‖ a ‖² + ‖ b ‖²)
  pair-norm X₀ X₁ a b p q = trans
    (cong₂ _+_ (‖‖²-cong {X₀} {a +ᴬ b} p) (‖‖²-cong {X₁} {a -ᴬ b} q))
    (parallelogram a b)

  if-double : (b : Bool) {X Y : ℤ} → X ≡ (+ 2) * Y →
              (if b then 0ℤ else X) ≡ (+ 2) * (if b then 0ℤ else Y)
  if-double true  _ = sym (*-zeroʳ (+ 2))
  if-double false p = p

colN-H : (w : Fin n) (ψ : Column n) → Respects ψ →
         colN (gateᴬ (H w) ψ) ≡ (+ 2) * colN ψ
colN-H w ψ resp =
  trans (Σᶻ-at w (λ z → ‖ gateᴬ (H w) ψ z ‖²) respF)
    (trans (Σᶻ-cong (λ z → if-double (z w) (pair z)))
      (trans (Σᶻ-* (+ 2) (λ z → if z w then 0ℤ else
                             (‖ ψ (z [ w ≔ false ]) ‖² +
                              ‖ ψ (z [ w ≔ true ]) ‖²)))
             (cong (λ u → (+ 2) * u)
                   (sym (Σᶻ-at w (λ z → ‖ ψ z ‖²) respG)))))
  where
  respF : RespectsZ (λ z → ‖ gateᴬ (H w) ψ z ‖²)
  respF z z′ zz = ‖‖²-cong (gateᴬ-resp (H w) resp z z′ zz)

  respG : RespectsZ (λ z → ‖ ψ z ‖²)
  respG z z′ zz = ‖‖²-cong (resp z z′ zz)

  e₀ : ∀ z → ½ * [ (z [ w ≔ false ]) w ]ᶻ ≡ 0ℤ
  e₀ z =
    trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w false)) (*-zeroʳ ½)

  e₁ : ∀ z → ½ * [ (z [ w ≔ true ]) w ]ᶻ ≡ 0ℤ + (+ rank)
  e₁ z = trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w true))
               (trans (*-identityʳ ½) (sym (+-identityˡ ½)))

  pair : ∀ z → ‖ gateᴬ (H w) ψ (z [ w ≔ false ]) ‖² +
               ‖ gateᴬ (H w) ψ (z [ w ≔ true ]) ‖² ≡
               (+ 2) * (‖ ψ (z [ w ≔ false ]) ‖² +
                        ‖ ψ (z [ w ≔ true ]) ‖²)
  pair z = pair-norm
    (gateᴬ (H w) ψ (z [ w ≔ false ])) (gateᴬ (H w) ψ (z [ w ≔ true ]))
    (ψ (z [ w ≔ false ])) (ψ (z [ w ≔ true ]))
    (sign-0 (ψ (z [ w ≔ false ] [ w ≔ false ])) (ψ (z [ w ≔ false ]))
            (ψ (z [ w ≔ false ] [ w ≔ true ])) (ψ (z [ w ≔ true ]))
            (½ * [ (z [ w ≔ false ]) w ]ᶻ)
            (resp _ _ (≔-≔ z w false false)) (e₀ z)
            (resp _ _ (≔-≔ z w false true)))
    (sign-1 (ψ (z [ w ≔ true ] [ w ≔ false ])) (ψ (z [ w ≔ false ]))
            (ψ (z [ w ≔ true ] [ w ≔ true ])) (ψ (z [ w ≔ true ]))
            (½ * [ (z [ w ≔ true ]) w ]ᶻ)
            (resp _ _ (≔-≔ z w true false)) (e₁ z)
            (resp _ _ (≔-≔ z w true true)))


------------------------------------------------------------------------
-- Circuits

private
  twice : ∀ k c → + (2 ^ k) * ((+ 2) * c) ≡ + (2 ^ suc k) * c
  twice k c = trans (sym (*-assoc (+ (2 ^ k)) (+ 2) c))
    (cong (_* c) (trans (*-comm (+ (2 ^ k)) (+ 2))
                        (sym (pos-* 2 (2 ^ k)))))

-- A circuit multiplies the norm of a column by 2^k, k the number of
-- its Hadamards.

colN-apply : (C : Circuit n) (ψ : Column n) → Respects ψ →
             colN (applyᴬ C ψ) ≡ + (2 ^ norm C) * colN ψ
colN-apply []               ψ resp = sym (*-identityˡ (colN ψ))
colN-apply (H w ∷ C)        ψ resp =
  trans (colN-apply C (gateᴬ (H w) ψ) (gateᴬ-resp (H w) resp))
    (trans (cong (λ u → + (2 ^ norm C) * u) (colN-H w ψ resp))
           (twice (norm C) (colN ψ)))
colN-apply (X w ∷ C)        ψ resp =
  trans (colN-apply C (gateᴬ (X w) ψ) (gateᴬ-resp (X w) resp))
        (cong (λ u → + (2 ^ norm C) * u) (colN-X w ψ resp))
colN-apply (CNOT c t p ∷ C) ψ resp =
  trans (colN-apply C (gateᴬ (CNOT c t p) ψ)
                    (gateᴬ-resp (CNOT c t p) resp))
        (cong (λ u → + (2 ^ norm C) * u) (colN-CNOT c t p ψ resp))
colN-apply (R k w ∷ C)      ψ resp =
  trans (colN-apply C (gateᴬ (R k w) ψ) (gateᴬ-resp (R k w) resp))
        (cong (λ u → + (2 ^ norm C) * u) (colN-R k w ψ))
colN-apply (R† k w ∷ C)     ψ resp =
  trans (colN-apply C (gateᴬ (R† k w) ψ) (gateᴬ-resp (R† k w) resp))
        (cong (λ u → + (2 ^ norm C) * u) (colN-R† k w ψ))

-- The basis column is a unit vector.

colN-δ : (x : Assign n) → colN (δ x) ≡ 1ℤ
colN-δ x =
  trans (Σᶻ-point (λ z → ‖ δ x z ‖²)
                  (λ z z′ zz → ‖‖²-cong (δ-resp x z z′ zz)) x)
    (trans (cong₂ _+_ here rest) (+-identityʳ 1ℤ))
  where
  here : ‖ δ x x ‖² ≡ 1ℤ
  here = trans
    (‖‖²-cong {δ x x} {zpow 0ℤ}
      (λ i → cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-refl x)))
    ‖zpow0‖²

  off : (b : Bool) →
        (if b then 0ℤ else ‖ (if b then zpow 0ℤ else 0ᴬ) ‖²) ≡ 0ℤ
  off true  = refl
  off false = ‖0ᴬ‖²

  rest : Σᶻ (λ z → if same x z then 0ℤ else ‖ δ x z ‖²) ≡ 0ℤ
  rest = trans (Σᶻ-cong (λ z → off (same x z))) Σᶻ-0

-- Every column of ⟦ C ⟧ has trace-form norm 2^(norm C).

⟦⟧-unit-columns : (C : Circuit n) (x : Assign n) →
                  Σᶻ (λ z → ‖ amp ⟦ C ⟧ x z ‖²) ≡ + (2 ^ norm C)
⟦⟧-unit-columns C x =
  trans (Σᶻ-cong (λ z →
          ‖‖²-cong {amp ⟦ C ⟧ x z} {applyᴬ C (δ x) z} (prop-2-10 C x z)))
    (trans (colN-apply C (δ x) (δ-resp x))
      (trans (cong (λ u → + (2 ^ norm C) * u) (colN-δ x))
             (*-identityʳ (+ (2 ^ norm C)))))

-- Hence lemma 4.1 holds for these circuits.

circuit-WellFormed : (C : Circuit n) → WellFormed ⟦ C ⟧
circuit-WellFormed C x = ≤-reflexive (⟦⟧-unit-columns C x)


------------------------------------------------------------------------
-- Gaussian elimination on circuits with X

-- ⟦ C ⟧ is the path-sum of the state the circuit runs to, whose forms
-- are affine; Gaussian elimination reifies its isometry restriction or
-- refutes the identity.

⟦⟧-state : (C : Circuit n) → ⟦ C ⟧ ≡ toPS (proj₂ (run C KC.init))
⟦⟧-state C = refl

Reification-WithX : Circuit n → Set
Reification-WithX {n} C =
  ¬ (⟦ C ⟧ ≋ idPS) ⊎
  ∃ λ m′ → ∃ λ (ξ′ : PathSum n (norm C) m′) →
    Internal ξ′ × (∀ w → out ξ′ w ≡ μ x[ w ]) ×
    (∀ {d} → Ord≤ d (phase ⟦ C ⟧) → Ord≤ d (phase ξ′)) ×
    (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)

reification-WithX : (C : Circuit n) → Reification-WithX C
reification-WithX C =
  reification {k = norm C} (proj₂ (run C KC.init)) (circuit-WellFormed C)
