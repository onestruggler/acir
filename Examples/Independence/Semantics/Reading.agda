------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake's qubit values read in 𝔻[ω], and completeness by transfer
--
-- A value (h , M) of Semantics.Qubit, M over ℤ[ω], is read in 𝔻[ω] =
-- ℤ[1/√2,i] as (1/√2)^h φ(M) (⟪_⟫, with φ of Clifford.Ring): an
-- operator of Real-Clifford.Semantics.Laws, and through
-- Real-Clifford.Semantics.Matrix a 2ⁿ × 2ⁿ matrix (Mat.mat), the
-- matrices the two-level developments over 𝔻[ω] use.  The reading
-- turns products into products (⟪⟫-∙, in the reverse order: values
-- compose in diagram order, operators in operator order), and equal
-- values give equal readings (Transfer.exact).
--
-- Transfer.Via is the semantic half of a completeness proof by
-- transfer (Blake, Section 4): given another presentation whose words
-- have matrices F, multiplicative and in operator order, and an
-- encoding ℰ of the gates of width n whose matrices are the gates'
-- readings, the encoding of a circuit (its gates' encodings in the
-- reverse order, ℰʷ) has the circuit's reading as its matrix
-- (bridge), so circuits with equal values have encodings with equal
-- matrices (transfer).  Transfer.ViaT is the same for an encoding that
-- keeps the order of the gates, whose matrix is then the transpose.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Semantics.Reading where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; RingD ; AdjointD ; isCommutativeRing-D ; adj-D ; √½)
open import Examples.Groups.Real-Clifford.Presentation.DOmega using (√½-sq)
import Examples.Groups.Real-Clifford.Semantics.Laws as RLaws
import Examples.Groups.Real-Clifford.Semantics.Interpretation as RInterp
import Examples.Groups.Real-Clifford.Semantics.Matrix as RMatrix
open import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra isCommutativeRing-D adj-D using (𝕀)

import Examples.Independence.Prop as Prop
import Examples.Independence.Semantics.Qubit as O
open O using (module ZΩ ; √2)
open import Examples.Independence.Clifford.Ring using (φ ; φ-+ ; φ-* ; φ-0 ; φ-1 ; √½-√2)

module RL = RLaws {A = D} {{RingD}} isCommutativeRing-D
module RI = RInterp {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq
module Mat = RMatrix {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D

open RL.AR using (_+_ ; _*_ ; 1# ; 0# ; +-identityʳ ; *-identityˡ ; zeroˡ ; *-assoc ; *-comm)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Digits and bits

dig : Bool → Fin 2
dig false = zero
dig true  = suc zero

digs : RL.Bits n → O.Digits n
digs []      = []
digs (b ∷ x) = dig b ∷ digs x

------------------------------------------------------------------------
-- Operators over ℤ[ω] read in 𝔻[ω]

Φ : O.Op n → RL.Op n
Φ M x y = φ (M (digs x) (digs y))

Φ-cong : {M N : O.Op n} → M O.≐ N → Φ M RL.≐ Φ N
Φ-cong e x y = Eq.cong φ (e (digs x) (digs y))

φΣ : (f : O.Digits n → ZΩ.Q) → φ (O.Σv f) ≡ RL.Σb (λ z → φ (f (digs z)))
φΣ {zero}  f = refl
φΣ {suc n} f =
  Eq.trans (φ-+ F₀ (F₁ ZΩ.+ ZΩ.0q))
    (Eq.trans (Eq.cong (φ F₀ +_) (Eq.trans (φ-+ F₁ ZΩ.0q) (+-identityʳ (φ F₁))))
              (Eq.cong₂ _+_ (φΣ (λ xs → f (zero ∷ xs))) (φΣ (λ xs → f (suc zero ∷ xs)))))
  where
  F₀ = O.Σv (λ xs → f (zero ∷ xs))
  F₁ = O.Σv (λ xs → f (suc zero ∷ xs))

Φ-⊙ : (M N : O.Op n) → Φ (M O.⊙ N) RL.≐ (Φ M RL.⊙ Φ N)
Φ-⊙ M N x y =
  Eq.trans (φΣ (λ z → M (digs x) z ZΩ.* N z (digs y)))
           (RL.Σ-cong (λ z → φ-* (M (digs x) (digs z)) (N (digs z) (digs y))))

Φ-δ : Φ (O.Idₒ {n}) RL.≐ RL.Idₒ
Φ-δ []           []           = refl
Φ-δ (true ∷ x)  (true ∷ y)  =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (false ∷ x) (false ∷ y) =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (true ∷ x)  (false ∷ y) = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)
Φ-δ (false ∷ x) (true ∷ y)  = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)

-- A value, read in 𝔻[ω].
⟪_⟫ : O.Sc n → RL.Op n
⟪ s ⟫ = RI.scale (√½ RI.^ proj₁ s) (Φ (O.ix (proj₂ s)))

private
  ^-swap : (a b : ℕ) → (√½ RI.^ a) * (√½ RI.^ b) ≡ √½ RI.^ (b +ℕ a)
  ^-swap a b = Eq.trans (*-comm _ _) (Eq.sym (RI.^-+ √½ b a))

-- The empty value is the identity, and a product of values the product
-- of their readings, in the other order.
⟪⟫-ε : ⟪ O.εs {n} ⟫ RL.≐ RL.Idₒ
⟪⟫-ε x y = Eq.trans (*-identityˡ _) (Eq.trans (Φ-cong O.ix-id x y) (Φ-δ x y))

⟪⟫-∙ : (s t : O.Sc n) → ⟪ t ⟫ RL.⊙ ⟪ s ⟫ RL.≐ ⟪ s O.∙ t ⟫
⟪⟫-∙ (hs , Ms) (ht , Mt) =
  RL.≐-trans (RI.scale-⊙ (√½ RI.^ ht) (√½ RI.^ hs) (Φ (O.ix Mt)) (Φ (O.ix Ms)))
  (RL.≐-trans (λ x y → Eq.cong (λ c → c * (Φ (O.ix Mt) RL.⊙ Φ (O.ix Ms)) x y) (^-swap ht hs))
  (RI.scale-cong (RL.≐-sym (RL.≐-trans (Φ-cong (O.ix-mul Mt Ms)) (Φ-⊙ (O.ix Mt) (O.ix Ms))))))

------------------------------------------------------------------------
-- Transposition
--
-- Every qubit gate here is a symmetric matrix, so a circuit read in
-- the other order has the transposed matrix: what a source that reads
-- its words in diagram order, without reversing them, sees (ViaT).

_ᵀ : RL.Op n → RL.Op n
(M ᵀ) x y = M y x

ᵀ-cong : {M N : RL.Op n} → M RL.≐ N → M ᵀ RL.≐ N ᵀ
ᵀ-cong e x y = e y x

ᵀ-⊙ : (M N : RL.Op n) → (M RL.⊙ N) ᵀ RL.≐ (N ᵀ RL.⊙ M ᵀ)
ᵀ-⊙ M N x y = RL.Σ-cong (λ z → *-comm (M y z) (N z x))

private
  δb-sym : (x y : RL.Bits n) → RL.δb x y ≡ RL.δb y x
  δb-sym []          []          = refl
  δb-sym (true ∷ x)  (true ∷ y)  = δb-sym x y
  δb-sym (false ∷ x) (false ∷ y) = δb-sym x y
  δb-sym (true ∷ x)  (false ∷ y) = refl
  δb-sym (false ∷ x) (true ∷ y)  = refl

Idₒ-ᵀ : RL.Idₒ {n} ᵀ RL.≐ RL.Idₒ
Idₒ-ᵀ x y = δb-sym y x

------------------------------------------------------------------------
-- Equal values, equal readings

private
  φ-^ : (a : ZΩ.Q) (k : ℕ) → φ (a O.^ k) ≡ φ a RI.^ k
  φ-^ a zero    = φ-1
  φ-^ a (suc k) = Eq.trans (φ-* a (a O.^ k)) (Eq.cong (φ a *_) (φ-^ a k))

  r = φ √2

  swap4 : (a b c d : D) → (a * b) * (c * d) ≡ (a * c) * (b * d)
  swap4 a b c d =
    Eq.trans (*-assoc a b (c * d))
    (Eq.trans (Eq.cong (a *_) (Eq.trans (Eq.sym (*-assoc b c d))
              (Eq.trans (Eq.cong (_* d) (*-comm b c)) (*-assoc c b d))))
              (Eq.sym (*-assoc a c (b * d))))

  -- (1/√2)^k √2^k = 1.
  cancel : (k : ℕ) → (√½ RI.^ k) * (r RI.^ k) ≡ 1#
  cancel zero    = *-identityˡ 1#
  cancel (suc k) = Eq.trans (swap4 √½ (√½ RI.^ k) r (r RI.^ k))
                     (Eq.trans (Eq.cong₂ _*_ √½-√2 (cancel k)) (*-identityˡ 1#))

  -- From r^a p = r^b q, (1/√2)^b p = (1/√2)^a q.
  unscale : (a b : ℕ) {p q : D} → (r RI.^ a) * p ≡ (r RI.^ b) * q →
            (√½ RI.^ b) * p ≡ (√½ RI.^ a) * q
  unscale a b {p} {q} e = begin
    (√½ RI.^ b) * p
      ≡⟨ Eq.sym (*-identityˡ _) ⟩
    1# * ((√½ RI.^ b) * p)
      ≡⟨ Eq.cong (_* ((√½ RI.^ b) * p)) (Eq.sym (cancel a)) ⟩
    ((√½ RI.^ a) * (r RI.^ a)) * ((√½ RI.^ b) * p)
      ≡⟨ swap4 (√½ RI.^ a) (r RI.^ a) (√½ RI.^ b) p ⟩
    ((√½ RI.^ a) * (√½ RI.^ b)) * ((r RI.^ a) * p)
      ≡⟨ Eq.cong (((√½ RI.^ a) * (√½ RI.^ b)) *_) e ⟩
    ((√½ RI.^ a) * (√½ RI.^ b)) * ((r RI.^ b) * q)
      ≡⟨ shuffle′ (√½ RI.^ a) (√½ RI.^ b) (r RI.^ b) q ⟩
    ((√½ RI.^ b) * (r RI.^ b)) * ((√½ RI.^ a) * q)
      ≡⟨ Eq.cong (_* ((√½ RI.^ a) * q)) (cancel b) ⟩
    1# * ((√½ RI.^ a) * q)
      ≡⟨ *-identityˡ _ ⟩
    (√½ RI.^ a) * q ∎
    where
    open Eq.≡-Reasoning
    shuffle′ : (a b c d : D) → (a * b) * (c * d) ≡ (b * c) * (a * d)
    shuffle′ a b c d =
      Eq.trans (Eq.cong (_* (c * d)) (*-comm a b)) (swap4 b a c d)

------------------------------------------------------------------------
-- Transfer, for the circuits of a gate set

module Transfer {Gate : ℕ → Set} (val : ∀ {k} → Prop.PGate Gate k → O.Sc k) where

  open Prop Gate using (Gen ; Circuit)
  open O.Circuits val using (⟦_⟧₀ ; ⟦_⟧ ; module Exact)

  exact : {s t : O.Sc n} → s Exact.≈ t → ⟪ s ⟫ RL.≐ ⟪ t ⟫
  exact {s = hs , Ms} {ht , Mt} (Exact.phased _ refl agree) x y =
    unscale ht hs (Eq.trans (Eq.sym L) (Eq.trans (Eq.cong φ (agree (digs x) (digs y))) R))
    where
    Fs = O.ix Ms (digs x) (digs y)
    Ft = O.ix Mt (digs x) (digs y)

    L : φ ((√2 O.^ ht) ZΩ.* Fs) ≡ (r RI.^ ht) * φ Fs
    L = Eq.trans (φ-* (√2 O.^ ht) Fs) (Eq.cong (_* φ Fs) (φ-^ √2 ht))

    R : φ (((O.x O.^ 0) ZΩ.* (√2 O.^ hs)) ZΩ.* Ft) ≡ (r RI.^ hs) * φ Ft
    R = Eq.trans (φ-* ((O.x O.^ 0) ZΩ.* (√2 O.^ hs)) Ft)
          (Eq.cong (_* φ Ft) (Eq.trans (φ-* (O.x O.^ 0) (√2 O.^ hs))
            (Eq.trans (Eq.cong₂ _*_ φ-1 (φ-^ √2 hs)) (*-identityˡ _))))

  -- Another presentation, its matrices in operator order, and an
  -- encoding of the gates of width n into its words.
  module Via {n : ℕ} {G : Set}
    (F   : Word G → Matrix (2 ^ n) (2 ^ n) D)
    (F-ε : F ε ≡ 𝕀)
    (F-• : ∀ u v → F (u • v) ≡ F u ·*· F v)
    (ℰ   : Gen n → Word G)
    (gen : ∀ g → F (ℰ g) ≡ Mat.mat ⟪ ⟦ g ⟧₀ ⟫)
    where

    -- A circuit: its gates encoded, in the reverse order.
    ℰʷ : Circuit n → Word G
    ℰʷ [ g ]ʷ  = ℰ g
    ℰʷ ε       = ε
    ℰʷ (w • v) = ℰʷ v • ℰʷ w

    -- The matrix of the encoding is the circuit's value, read.
    bridge : (w : Circuit n) → F (ℰʷ w) ≡ Mat.mat ⟪ ⟦ w ⟧ ⟫
    bridge [ g ]ʷ  = gen g
    bridge ε       =
      Eq.trans F-ε (Eq.sym (Eq.trans (Mat.mat-≐ {n} (⟪⟫-ε {n})) (Mat.mat-Id {n})))
    bridge (w • v) =
      Eq.trans (F-• (ℰʷ v) (ℰʷ w))
      (Eq.trans (Eq.cong₂ _·*·_ (bridge v) (bridge w))
      (Eq.trans (Eq.sym (Mat.mat-⊙ ⟪ ⟦ v ⟧ ⟫ ⟪ ⟦ w ⟧ ⟫))
                (Mat.mat-≐ (⟪⟫-∙ ⟦ w ⟧ ⟦ v ⟧))))

    -- Circuits with equal values have encodings with equal matrices.
    transfer : {w v : Circuit n} → ⟦ w ⟧ Exact.≈ ⟦ v ⟧ → F (ℰʷ w) ≡ F (ℰʷ v)
    transfer {w} {v} e =
      Eq.trans (bridge w) (Eq.trans (Mat.mat-≐ (exact e)) (Eq.sym (bridge v)))

  -- The same for an encoding that keeps the order of the gates, into
  -- a presentation whose words are read in operator order: the
  -- encoding of a circuit has its transposed matrix, given the gates'.
  module ViaT {n : ℕ} {G : Set}
    (F   : Word G → Matrix (2 ^ n) (2 ^ n) D)
    (F-ε : F ε ≡ 𝕀)
    (F-• : ∀ u v → F (u • v) ≡ F u ·*· F v)
    (ℰ   : Gen n → Word G)
    (gen : ∀ g → F (ℰ g) ≡ Mat.mat (⟪ ⟦ g ⟧₀ ⟫ ᵀ))
    where

    ℰʷ : Circuit n → Word G
    ℰʷ [ g ]ʷ  = ℰ g
    ℰʷ ε       = ε
    ℰʷ (w • v) = ℰʷ w • ℰʷ v

    bridge : (w : Circuit n) → F (ℰʷ w) ≡ Mat.mat (⟪ ⟦ w ⟧ ⟫ ᵀ)
    bridge [ g ]ʷ  = gen g
    bridge ε       =
      Eq.trans F-ε (Eq.sym (Eq.trans (Mat.mat-≐ {n} (RL.≐-trans (ᵀ-cong (⟪⟫-ε {n})) Idₒ-ᵀ))
                                     (Mat.mat-Id {n})))
    bridge (w • v) =
      Eq.trans (F-• (ℰʷ w) (ℰʷ v))
      (Eq.trans (Eq.cong₂ _·*·_ (bridge w) (bridge v))
      (Eq.trans (Eq.sym (Mat.mat-⊙ (⟪ ⟦ w ⟧ ⟫ ᵀ) (⟪ ⟦ v ⟧ ⟫ ᵀ)))
                (Mat.mat-≐ (RL.≐-trans (RL.≐-sym (ᵀ-⊙ ⟪ ⟦ v ⟧ ⟫ ⟪ ⟦ w ⟧ ⟫))
                                       (ᵀ-cong (⟪⟫-∙ ⟦ w ⟧ ⟦ v ⟧))))))

    transfer : {w v : Circuit n} → ⟦ w ⟧ Exact.≈ ⟦ v ⟧ → F (ℰʷ w) ≡ F (ℰʷ v)
    transfer {w} {v} e =
      Eq.trans (bridge w) (Eq.trans (Mat.mat-≐ (ᵀ-cong (exact e))) (Eq.sym (bridge v)))
