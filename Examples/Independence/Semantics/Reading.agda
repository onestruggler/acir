------------------------------------------------------------------------
-- Presentations of groups
--
-- Qubit circuit values read in 𝔻[ω]
--
-- The part of the completeness bridges that does not depend on the
-- fragment: a value (h , M) of Examples.Independence.Semantics.Qubit,
-- M over ℤ[ω], read as the operator (1/√2)^h φ(M) over 𝔻[ω] (⟪_⟫,
-- φ from Clifford.Ring), with its laws (a composite is a product, the
-- second value's reading on the left; ⟪ε⟫), transposes, and Exactness:
-- for any gate valuation, circuits with exactly equal values have equal
-- readings (exact).  Clifford+CS.Bridge uses it; Clifford.Bridge and
-- Clifford+T.Bridge carry copies of the same text.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Semantics.Reading where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; RingD ; AdjointD ; isCommutativeRing-D ; adj-D ; √½ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; 1ᴰ)
import Examples.Groups.Real-Clifford.Semantics.Interpretation as QInterp
import Examples.Groups.Real-Clifford.Semantics.Laws as QLaws
import Examples.Groups.Real-Clifford.Semantics.Matrix as QMatrix
import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra as MatrixAlgebra

import Examples.Independence.Prop as Prop
open Prop using (PGate)
import Examples.Independence.Semantics.Qubit as O
open O using (module ZΩ ; √2)
open import Examples.Independence.Clifford.Ring using (φ ; φ-+ ; φ-* ; φ-0 ; φ-1 ; √½-√2)

-- (1/√2)² + (1/√2)² = 1, by computation.
opaque
  unfolding _+ᴰ_ _*ᴰ_

  √½-sq : √½ *ᴰ √½ +ᴰ √½ *ᴰ √½ ≡ 1ᴰ
  √½-sq = refl

module QI where
  open QLaws {A = D} {{RingD}} isCommutativeRing-D public
  open QInterp {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq public
module QM = QMatrix {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D
module MA = MatrixAlgebra {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D

open QI.AR using (_+_ ; _*_ ; 1# ; 0# ; +-identityʳ ; *-identityˡ ; *-identityʳ ;
                  zeroˡ ; zeroʳ ; *-assoc ; *-comm)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Digits and bits

dig : Bool → Fin 2
dig false = zero
dig true  = suc zero

digs : QI.Bits n → O.Digits n
digs []      = []
digs (b ∷ x) = dig b ∷ digs x

------------------------------------------------------------------------
-- Cliff₂'s operators read in 𝔻[ω]

Φ : O.Op n → QI.Op n
Φ M x y = φ (M (digs x) (digs y))

Φ-cong : {M N : O.Op n} → M O.≐ N → Φ M QI.≐ Φ N
Φ-cong e x y = Eq.cong φ (e (digs x) (digs y))

φΣ : (f : O.Digits n → ZΩ.Q) → φ (O.Σv f) ≡ QI.Σb (λ z → φ (f (digs z)))
φΣ {zero}  f = refl
φΣ {suc n} f =
  Eq.trans (φ-+ F₀ (F₁ ZΩ.+ ZΩ.0q))
    (Eq.trans (Eq.cong (φ F₀ +_) (Eq.trans (φ-+ F₁ ZΩ.0q) (+-identityʳ (φ F₁))))
              (Eq.cong₂ _+_ (φΣ (λ xs → f (zero ∷ xs))) (φΣ (λ xs → f (suc zero ∷ xs)))))
  where
  F₀ = O.Σv (λ xs → f (zero ∷ xs))
  F₁ = O.Σv (λ xs → f (suc zero ∷ xs))

Φ-⊙ : (M N : O.Op n) → Φ (M O.⊙ N) QI.≐ (Φ M QI.⊙ Φ N)
Φ-⊙ M N x y =
  Eq.trans (φΣ (λ z → M (digs x) z ZΩ.* N z (digs y)))
           (QI.Σ-cong (λ z → φ-* (M (digs x) (digs z)) (N (digs z) (digs y))))

Φ-δ : Φ (O.Idₒ {n}) QI.≐ QI.Idₒ
Φ-δ []           []           = refl
Φ-δ (true ∷ x)  (true ∷ y)  =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (false ∷ x) (false ∷ y) =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (true ∷ x)  (false ∷ y) = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)
Φ-δ (false ∷ x) (true ∷ y)  = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)

Φ-tensor : {m : ℕ} (M : O.Op m) (N : O.Op n) → Φ (O.tensor M N) QI.≐ QI.tensor (Φ M) (Φ N)
Φ-tensor {m = zero}  M N x       y       = φ-* (M [] []) (N (digs x) (digs y))
Φ-tensor {m = suc m} M N (a ∷ x) (b ∷ y) =
  Φ-tensor {m = m} (λ u v → M (dig a ∷ u) (dig b ∷ v)) N x y

Φ-emb : (M : O.Op k) → Φ (O.emb {k} {n} M) QI.≐ QI.emb {k} {n} (Φ M)
Φ-emb {k} {n} M = QI.≐-trans (Φ-tensor M (O.Idₒ {n})) (QI.tensor-cong {m = k} {n = n} (QI.≐-refl _) Φ-δ)

Φ-up : (M : O.Op n) → Φ (O.up M) QI.≐ QI.up (Φ M)
Φ-up {n} M = QI.≐-trans (Φ-tensor (O.Idₒ {1}) M) (QI.tensor-cong {m = 1} {n = n} Φ-δ (QI.≐-refl _))

Φ-scal : (c : ZΩ.Q) → Φ (O.scal {n} c) QI.≐ QI.scal (φ c)
Φ-scal c x y = Eq.trans (φ-* c (O.δv (digs x) (digs y))) (Eq.cong (φ c *_) (Φ-δ x y))

-- A value of Cliff₂, read in 𝔻[ω].
⟪_⟫ : O.Sc n → QI.Op n
⟪ s ⟫ = QI.scale (√½ QI.^ proj₁ s) (Φ (O.ix (proj₂ s)))


private
  scale-1 : (M : QI.Op n) → QI.scale 1# M QI.≐ M
  scale-1 M x y = *-identityˡ (M x y)

  ^-swap : (a b : ℕ) → (√½ QI.^ a) * (√½ QI.^ b) ≡ √½ QI.^ (b +ℕ a)
  ^-swap a b = Eq.trans (*-comm _ _) (Eq.sym (QI.^-+ √½ b a))

-- The reading of a composite is the product of the readings, the
-- second gate's on the left.
⟪∙⟫ : (s t : O.Sc n) → ⟪ s O.∙ t ⟫ QI.≐ (⟪ t ⟫ QI.⊙ ⟪ s ⟫)
⟪∙⟫ (hs , Ms) (ht , Mt) = QI.≐-sym
  (QI.≐-trans (QI.scale-⊙ (√½ QI.^ ht) (√½ QI.^ hs) (Φ (O.ix Mt)) (Φ (O.ix Ms)))
  (QI.≐-trans (λ x y → Eq.cong (λ c → c * (Φ (O.ix Mt) QI.⊙ Φ (O.ix Ms)) x y) (^-swap ht hs))
  (QI.scale-cong (QI.≐-sym (QI.≐-trans (Φ-cong (O.ix-mul Mt Ms)) (Φ-⊙ (O.ix Mt) (O.ix Ms)))))))

⟪ε⟫ : ⟪ O.εs {n} ⟫ QI.≐ QI.Idₒ
⟪ε⟫ = QI.≐-trans (scale-1 _) (QI.≐-trans (Φ-cong O.ix-id) Φ-δ)

------------------------------------------------------------------------
-- Transposes

_ᵀ : QI.Op n → QI.Op n
(M ᵀ) x y = M y x

ᵀ-cong : {M N : QI.Op n} → M QI.≐ N → (M ᵀ) QI.≐ (N ᵀ)
ᵀ-cong e x y = e y x

ᵀ-⊙ : (M N : QI.Op n) → ((M QI.⊙ N) ᵀ) QI.≐ ((N ᵀ) QI.⊙ (M ᵀ))
ᵀ-⊙ M N x y = QI.Σ-cong (λ z → *-comm (M y z) (N z x))

private
  δb-sym : (x y : QI.Bits n) → QI.δb x y ≡ QI.δb y x
  δb-sym []          []          = refl
  δb-sym (true ∷ x)  (true ∷ y)  = δb-sym x y
  δb-sym (false ∷ x) (false ∷ y) = δb-sym x y
  δb-sym (true ∷ x)  (false ∷ y) = refl
  δb-sym (false ∷ x) (true ∷ y)  = refl

ᵀ-Id : ((QI.Idₒ {n}) ᵀ) QI.≐ QI.Idₒ
ᵀ-Id x y = δb-sym y x

------------------------------------------------------------------------
-- Equal values, equal readings

private
  φ-^ : (a : ZΩ.Q) (k : ℕ) → φ (a O.^ k) ≡ φ a QI.^ k
  φ-^ a zero    = φ-1
  φ-^ a (suc k) = Eq.trans (φ-* a (a O.^ k)) (Eq.cong (φ a *_) (φ-^ a k))

  r = φ √2

  -- (1/√2)^k √2^k = 1.
  cancel : (k : ℕ) → (√½ QI.^ k) * (r QI.^ k) ≡ 1#
  cancel zero    = *-identityˡ 1#
  cancel (suc k) = Eq.trans (swap4 √½ (√½ QI.^ k) r (r QI.^ k))
                     (Eq.trans (Eq.cong₂ _*_ √½-√2 (cancel k)) (*-identityˡ 1#))
    where
    swap4 : (a b c d : D) → (a * b) * (c * d) ≡ (a * c) * (b * d)
    swap4 a b c d =
      Eq.trans (*-assoc a b (c * d))
      (Eq.trans (Eq.cong (a *_) (Eq.trans (Eq.sym (*-assoc b c d))
                (Eq.trans (Eq.cong (_* d) (*-comm b c)) (*-assoc c b d))))
                (Eq.sym (*-assoc a c (b * d))))

  -- From r^a F = r^b G, (1/√2)^b F = (1/√2)^a G.
  unscale : (a b : ℕ) {F G : D} → (r QI.^ a) * F ≡ (r QI.^ b) * G →
            (√½ QI.^ b) * F ≡ (√½ QI.^ a) * G
  unscale a b {F} {G} e = begin
    (√½ QI.^ b) * F
      ≡⟨ Eq.sym (*-identityˡ _) ⟩
    1# * ((√½ QI.^ b) * F)
      ≡⟨ Eq.cong (_* ((√½ QI.^ b) * F)) (Eq.sym (cancel a)) ⟩
    ((√½ QI.^ a) * (r QI.^ a)) * ((√½ QI.^ b) * F)
      ≡⟨ shuffle (√½ QI.^ a) (r QI.^ a) (√½ QI.^ b) F ⟩
    ((√½ QI.^ a) * (√½ QI.^ b)) * ((r QI.^ a) * F)
      ≡⟨ Eq.cong (((√½ QI.^ a) * (√½ QI.^ b)) *_) e ⟩
    ((√½ QI.^ a) * (√½ QI.^ b)) * ((r QI.^ b) * G)
      ≡⟨ shuffle′ (√½ QI.^ a) (√½ QI.^ b) (r QI.^ b) G ⟩
    ((√½ QI.^ b) * (r QI.^ b)) * ((√½ QI.^ a) * G)
      ≡⟨ Eq.cong (_* ((√½ QI.^ a) * G)) (cancel b) ⟩
    1# * ((√½ QI.^ a) * G)
      ≡⟨ *-identityˡ _ ⟩
    (√½ QI.^ a) * G ∎
    where
    open Eq.≡-Reasoning
    shuffle : (a b c d : D) → (a * b) * (c * d) ≡ (a * c) * (b * d)
    shuffle a b c d =
      Eq.trans (*-assoc a b (c * d))
      (Eq.trans (Eq.cong (a *_) (Eq.trans (Eq.sym (*-assoc b c d))
                (Eq.trans (Eq.cong (_* d) (*-comm b c)) (*-assoc c b d))))
                (Eq.sym (*-assoc a c (b * d))))
    shuffle′ : (a b c d : D) → (a * b) * (c * d) ≡ (b * c) * (a * d)
    shuffle′ a b c d =
      Eq.trans (Eq.cong (_* (c * d)) (*-comm a b)) (shuffle b a c d)

module Exactness {Gate : ℕ → Set} (val : ∀ {k} → PGate Gate k → O.Sc k) where

  open O.Circuits val using (⟦_⟧ ; module Exact)
  open Exact using (_≈_)
  open Prop Gate using (Circuit)

  exact : {w v : Circuit n} → ⟦ w ⟧ ≈ ⟦ v ⟧ → ⟪ ⟦ w ⟧ ⟫ QI.≐ ⟪ ⟦ v ⟧ ⟫
  exact {w = w} {v} (Exact.phased _ refl agree) x y =
    unscale hv hw (Eq.trans (Eq.sym L) (Eq.trans (Eq.cong φ (agree (digs x) (digs y))) R))
    where
    hw = proj₁ ⟦ w ⟧
    hv = proj₁ ⟦ v ⟧
    Fw = O.ix (proj₂ ⟦ w ⟧) (digs x) (digs y)
    Fv = O.ix (proj₂ ⟦ v ⟧) (digs x) (digs y)

    L : φ ((√2 O.^ hv) ZΩ.* Fw) ≡ (r QI.^ hv) * φ Fw
    L = Eq.trans (φ-* (√2 O.^ hv) Fw) (Eq.cong (_* φ Fw) (φ-^ √2 hv))

    R : φ (((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) ZΩ.* Fv) ≡ (r QI.^ hw) * φ Fv
    R = Eq.trans (φ-* ((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) Fv)
          (Eq.cong (_* φ Fv) (Eq.trans (φ-* (O.x O.^ 0) (√2 O.^ hw))
            (Eq.trans (Eq.cong₂ _*_ φ-1 (φ-^ √2 hw)) (*-identityˡ _))))
