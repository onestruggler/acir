------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffT₂'s matrices against the sources' on one and two qubits
--
-- Bian and Selinger's presentation of 2-qubit Clifford+T operators
-- (Examples.Groups.Clifford+T-2qubit) reads its words over W, H0, H1,
-- S0, S1, T0, T1 and CZ as 4 × 4 matrices over 𝔻[ω], in operator
-- order, through Greylyn's two-level generators; Greylyn's presentation
-- of U₂(ℤ[1/√2, i]) (Examples.Groups.Clifford+T-2qubit-TwoLevel at
-- n = 2) reads two-level words as 2 × 2 ones.  Both are complete.  The
-- decodings Dʷ (two wires: their qubit k on wire k, S as T², CZ as
-- H CNOT H on wire 0) and Dʷ₁ (one wire: ω on |1⟩ as T, on |0⟩ as
-- X T X) read their words letter for letter: every gate matrix is
-- symmetric, so reading a word in diagram order rather than operator
-- order transposes its matrix.  So bridge₂ and bridge₁ say that their
-- matrix of a word is the matrix (Real-Clifford.Semantics.Matrix's mat,
-- wire 0 the most significant bit, as their qubit 0 is) of the
-- transpose of its decoding's reading (1/√2)^h φ(M) in 𝔻[ω] (⟪_⟫, as in
-- Clifford.Bridge): their generators are compared entry by entry, by
-- evaluation on the transparent products of two-level matrices (gm),
-- and a product is a product on both sides.  The encodings ℰʷ and ℰ₁ʷ
-- send CliffT₂'s circuits to their words; Completeness reads their
-- matrices through the decoding, by Lemma 19.  Equal matrices of
-- CliffT₂ give equal readings (exact).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.Bridge where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥)
import Data.Empty.Irrelevant as Irr
open import Data.Fin.Base as Fin using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; s≤s ; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; RingD ; AdjointD ; isCommutativeRing-D ; adj-D ; √½ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics as TLS
open import Examples.Groups.Real-Clifford.Presentation.DOmega using (√½-sq)
import Examples.Groups.Real-Clifford.Semantics.Interpretation as QInterp
import Examples.Groups.Real-Clifford.Semantics.Laws as QLaws
import Examples.Groups.Real-Clifford.Semantics.Matrix as QMatrix
import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra as MatrixAlgebra
open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
import Examples.Groups.Clifford+T-2qubit.Presentation as BS

open import Examples.Independence.Clifford+T.Syntactics
import Examples.Independence.Clifford+T.Semantics as Sem
import Examples.Independence.Semantics.Qubit as O
open O using (module ZΩ ; √2)
open import Examples.Independence.Clifford.Ring using (φ ; φ-+ ; φ-* ; φ-0 ; φ-1 ; √½-√2)

module QI where
  open QLaws {A = D} {{RingD}} isCommutativeRing-D public
  open QInterp {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq public
module QM = QMatrix {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D
module MA = MatrixAlgebra {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D
module C = Clifford+T

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
-- The matrix of a two-level word

-- The product of its generators' matrices: transparent, where ⟦_⟧ᵐ acts
-- through the opaque actV.
gm : {m : ℕ} → Word (TL.Gen m) → Matrix m m D
gm [ g ]ʷ  = TLS.gmat g
gm ε       = TLS.⟦ ε ⟧ᵐ
gm (u • v) = gm u ·*· gm v

⟦⟧≡gm : {m : ℕ} (u : Word (TL.Gen m)) → TLS.⟦ u ⟧ᵐ ≡ gm u
⟦⟧≡gm [ g ]ʷ  = TLS.⟦g⟧ᵐ≡ g
⟦⟧≡gm ε       = refl
⟦⟧≡gm (u • v) = Eq.trans (TLS.⟦•⟧ᵐ u v) (Eq.cong₂ _·*·_ (⟦⟧≡gm u) (⟦⟧≡gm v))

------------------------------------------------------------------------
-- Two wires: the encoding, and their words decoded

ℰ : Gen 2 → Word C.Generator
ℰ (gate₀ ⌈ ω-gate ⌉) = C.W
ℰ (gate₁ ⌈ H-gate ⌉) = C.H0
ℰ (gate₁ ⌈ T-gate ⌉) = C.T0
ℰ (gate₂ ⌈ CX-gate ⌉) = C.H0 • C.CZ • C.H0
ℰ (gate₂ swap) = C.Swap
ℰ (gate₀ ⌈ ω-gate ⌉ ↥) = C.W
ℰ (gate₁ ⌈ H-gate ⌉ ↥) = C.H1
ℰ (gate₁ ⌈ T-gate ⌉ ↥) = C.T1
ℰ ((gate₀ ⌈ ω-gate ⌉ ↥) ↥) = C.W

-- A circuit: its gates encoded, in the same order.
ℰʷ : Circuit 2 → Word C.Generator
ℰʷ [ g ]ʷ  = ℰ g
ℰʷ ε       = ε
ℰʷ (w • v) = ℰʷ w • ℰʷ v

-- Their qubit k on wire k, S as T², CZ as H CNOT H on wire 0.
D₀ : C.Generator → Circuit 2
D₀ C.W-gen  = ω
D₀ C.H0-gen = H
D₀ C.H1-gen = H ↑
D₀ C.S0-gen = S
D₀ C.S1-gen = S ↑
D₀ C.T0-gen = T
D₀ C.T1-gen = T ↑
D₀ C.CZ-gen = H • CX • H

-- A word of theirs, letter for letter.
Dʷ : Word C.Generator → Circuit 2
Dʷ [ g ]ʷ  = D₀ g
Dʷ ε       = ε
Dʷ (w • v) = Dʷ w • Dʷ v

-- Their generators, entry by entry.
opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  entries₂ : (x : C.Generator) (r c : Fin 4) →
             MA.ent (gm (BS.tl x)) r c ≡ MA.ent (QM.mat (⟪ Sem.⟦ D₀ x ⟧ ⟫ ᵀ)) r c
  entries₂ C.W-gen zero zero = refl
  entries₂ C.W-gen zero (suc zero) = refl
  entries₂ C.W-gen zero (suc (suc zero)) = refl
  entries₂ C.W-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.W-gen (suc zero) zero = refl
  entries₂ C.W-gen (suc zero) (suc zero) = refl
  entries₂ C.W-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.W-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.W-gen (suc (suc zero)) zero = refl
  entries₂ C.W-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.W-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.W-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.W-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.W-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.W-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.W-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries₂ C.H0-gen zero zero = refl
  entries₂ C.H0-gen zero (suc zero) = refl
  entries₂ C.H0-gen zero (suc (suc zero)) = refl
  entries₂ C.H0-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.H0-gen (suc zero) zero = refl
  entries₂ C.H0-gen (suc zero) (suc zero) = refl
  entries₂ C.H0-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.H0-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.H0-gen (suc (suc zero)) zero = refl
  entries₂ C.H0-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.H0-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.H0-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.H0-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.H0-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.H0-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.H0-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries₂ C.H1-gen zero zero = refl
  entries₂ C.H1-gen zero (suc zero) = refl
  entries₂ C.H1-gen zero (suc (suc zero)) = refl
  entries₂ C.H1-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.H1-gen (suc zero) zero = refl
  entries₂ C.H1-gen (suc zero) (suc zero) = refl
  entries₂ C.H1-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.H1-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.H1-gen (suc (suc zero)) zero = refl
  entries₂ C.H1-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.H1-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.H1-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.H1-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.H1-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.H1-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.H1-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries₂ C.S0-gen zero zero = refl
  entries₂ C.S0-gen zero (suc zero) = refl
  entries₂ C.S0-gen zero (suc (suc zero)) = refl
  entries₂ C.S0-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.S0-gen (suc zero) zero = refl
  entries₂ C.S0-gen (suc zero) (suc zero) = refl
  entries₂ C.S0-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.S0-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.S0-gen (suc (suc zero)) zero = refl
  entries₂ C.S0-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.S0-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.S0-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.S0-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.S0-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.S0-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.S0-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries₂ C.S1-gen zero zero = refl
  entries₂ C.S1-gen zero (suc zero) = refl
  entries₂ C.S1-gen zero (suc (suc zero)) = refl
  entries₂ C.S1-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.S1-gen (suc zero) zero = refl
  entries₂ C.S1-gen (suc zero) (suc zero) = refl
  entries₂ C.S1-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.S1-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.S1-gen (suc (suc zero)) zero = refl
  entries₂ C.S1-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.S1-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.S1-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.S1-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.S1-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.S1-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.S1-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries₂ C.T0-gen zero zero = refl
  entries₂ C.T0-gen zero (suc zero) = refl
  entries₂ C.T0-gen zero (suc (suc zero)) = refl
  entries₂ C.T0-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.T0-gen (suc zero) zero = refl
  entries₂ C.T0-gen (suc zero) (suc zero) = refl
  entries₂ C.T0-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.T0-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.T0-gen (suc (suc zero)) zero = refl
  entries₂ C.T0-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.T0-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.T0-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.T0-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.T0-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.T0-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.T0-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries₂ C.T1-gen zero zero = refl
  entries₂ C.T1-gen zero (suc zero) = refl
  entries₂ C.T1-gen zero (suc (suc zero)) = refl
  entries₂ C.T1-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.T1-gen (suc zero) zero = refl
  entries₂ C.T1-gen (suc zero) (suc zero) = refl
  entries₂ C.T1-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.T1-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.T1-gen (suc (suc zero)) zero = refl
  entries₂ C.T1-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.T1-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.T1-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.T1-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.T1-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.T1-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.T1-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries₂ C.CZ-gen zero zero = refl
  entries₂ C.CZ-gen zero (suc zero) = refl
  entries₂ C.CZ-gen zero (suc (suc zero)) = refl
  entries₂ C.CZ-gen zero (suc (suc (suc zero))) = refl
  entries₂ C.CZ-gen (suc zero) zero = refl
  entries₂ C.CZ-gen (suc zero) (suc zero) = refl
  entries₂ C.CZ-gen (suc zero) (suc (suc zero)) = refl
  entries₂ C.CZ-gen (suc zero) (suc (suc (suc zero))) = refl
  entries₂ C.CZ-gen (suc (suc zero)) zero = refl
  entries₂ C.CZ-gen (suc (suc zero)) (suc zero) = refl
  entries₂ C.CZ-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries₂ C.CZ-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries₂ C.CZ-gen (suc (suc (suc zero))) zero = refl
  entries₂ C.CZ-gen (suc (suc (suc zero))) (suc zero) = refl
  entries₂ C.CZ-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries₂ C.CZ-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl

-- Their matrix of any word is the transpose of CliffT₂'s matrix of its
-- decoding, read in 𝔻[ω].
bridge₂ : (u : Word C.Generator) → proj₁ BS.⟦ u ⟧ ≡ QM.mat (⟪ Sem.⟦ Dʷ u ⟧ ⟫ ᵀ)
bridge₂ [ x ]ʷ  = Eq.trans (⟦⟧≡gm (BS.tl x)) (MA.mat-ext (entries₂ x))
bridge₂ ε       = Eq.sym (Eq.trans (QM.mat-≐ {n = 2} (QI.≐-trans (ᵀ-cong ⟪ε⟫) ᵀ-Id)) (QM.mat-Id {n = 2}))
bridge₂ (u • v) =
  Eq.trans (TLS.⟦•⟧ᵐ ((BS.tl ʷ) u) ((BS.tl ʷ) v))
  (Eq.trans (Eq.cong₂ _·*·_ (bridge₂ u) (bridge₂ v))
  (Eq.trans (Eq.sym (QM.mat-⊙ (⟪ Sem.⟦ Dʷ u ⟧ ⟫ ᵀ) (⟪ Sem.⟦ Dʷ v ⟧ ⟫ ᵀ)))
  (QM.mat-≐ (QI.≐-trans (QI.≐-sym (ᵀ-⊙ ⟪ Sem.⟦ Dʷ v ⟧ ⟫ ⟪ Sem.⟦ Dʷ u ⟧ ⟫))
                        (ᵀ-cong (QI.≐-sym (⟪∙⟫ Sem.⟦ Dʷ u ⟧ Sem.⟦ Dʷ v ⟧)))))))

------------------------------------------------------------------------
-- One wire: Greylyn's two-level generators on two indices

-- 1 < 1 is empty (for the refutations below).
lt11 : Fin._<_ (Fin.suc (Fin.zero {0})) (Fin.suc (Fin.zero {0})) → ⊥
lt11 (s≤s ())

01< : Fin._<_ (Fin.zero {1}) (Fin.suc (Fin.zero {0}))
01< = s≤s z≤n

ℰ₁ : Gen 1 → Word (TL.Gen 2)
ℰ₁ (gate₀ ⌈ ω-gate ⌉)    = TL.ω zero • TL.ω (suc zero)
ℰ₁ (gate₁ ⌈ H-gate ⌉)    = TL.H zero (suc zero) 01<
ℰ₁ (gate₁ ⌈ T-gate ⌉)    = TL.ω (suc zero)
ℰ₁ (gate₀ ⌈ ω-gate ⌉ ↥)  = TL.ω zero • TL.ω (suc zero)

ℰ₁ʷ : Circuit 1 → Word (TL.Gen 2)
ℰ₁ʷ [ g ]ʷ  = ℰ₁ g
ℰ₁ʷ ε       = ε
ℰ₁ʷ (w • v) = ℰ₁ʷ w • ℰ₁ʷ v

-- ω on |1⟩ is T, ω on |0⟩ is X T X; X and H are themselves.
D₁ : TL.Gen 2 → Circuit 1
D₁ (TL.X-gen _ _ _)      = X
D₁ (TL.K-gen _ _ _)      = H
D₁ (TL.i-gen zero)       = X • T • X
D₁ (TL.i-gen (suc zero)) = T

Dʷ₁ : Word (TL.Gen 2) → Circuit 1
Dʷ₁ [ g ]ʷ  = D₁ g
Dʷ₁ ε       = ε
Dʷ₁ (w • v) = Dʷ₁ w • Dʷ₁ v

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  entries₁ : (y : TL.Gen 2) (r c : Fin 2) →
             MA.ent (TLS.gmat y) r c ≡ MA.ent (QM.mat (⟪ Sem.⟦ D₁ y ⟧ ⟫ ᵀ)) r c
  entries₁ (TL.X-gen zero (suc zero) _) zero zero = refl
  entries₁ (TL.X-gen zero (suc zero) _) zero (suc zero) = refl
  entries₁ (TL.X-gen zero (suc zero) _) (suc zero) zero = refl
  entries₁ (TL.X-gen zero (suc zero) _) (suc zero) (suc zero) = refl
  entries₁ (TL.K-gen zero (suc zero) _) zero zero = refl
  entries₁ (TL.K-gen zero (suc zero) _) zero (suc zero) = refl
  entries₁ (TL.K-gen zero (suc zero) _) (suc zero) zero = refl
  entries₁ (TL.K-gen zero (suc zero) _) (suc zero) (suc zero) = refl
  entries₁ (TL.i-gen zero) zero zero = refl
  entries₁ (TL.i-gen zero) zero (suc zero) = refl
  entries₁ (TL.i-gen zero) (suc zero) zero = refl
  entries₁ (TL.i-gen zero) (suc zero) (suc zero) = refl
  entries₁ (TL.i-gen (suc zero)) zero zero = refl
  entries₁ (TL.i-gen (suc zero)) zero (suc zero) = refl
  entries₁ (TL.i-gen (suc zero)) (suc zero) zero = refl
  entries₁ (TL.i-gen (suc zero)) (suc zero) (suc zero) = refl
  entries₁ (TL.X-gen zero zero ()) _ _
  entries₁ (TL.X-gen (suc zero) zero ()) _ _
  entries₁ (TL.X-gen (suc zero) (suc zero) p) _ _ = Irr.⊥-elim (lt11 p)
  entries₁ (TL.K-gen zero zero ()) _ _
  entries₁ (TL.K-gen (suc zero) zero ()) _ _
  entries₁ (TL.K-gen (suc zero) (suc zero) p) _ _ = Irr.⊥-elim (lt11 p)

bridge₁ : (u : Word (TL.Gen 2)) → TLS.⟦ u ⟧ᵐ ≡ QM.mat (⟪ Sem.⟦ Dʷ₁ u ⟧ ⟫ ᵀ)
bridge₁ [ y ]ʷ  = Eq.trans (TLS.⟦g⟧ᵐ≡ y) (MA.mat-ext (entries₁ y))
bridge₁ ε       = Eq.sym (Eq.trans (QM.mat-≐ {n = 1} (QI.≐-trans (ᵀ-cong ⟪ε⟫) ᵀ-Id)) (QM.mat-Id {n = 1}))
bridge₁ (u • v) =
  Eq.trans (TLS.⟦•⟧ᵐ u v)
  (Eq.trans (Eq.cong₂ _·*·_ (bridge₁ u) (bridge₁ v))
  (Eq.trans (Eq.sym (QM.mat-⊙ (⟪ Sem.⟦ Dʷ₁ u ⟧ ⟫ ᵀ) (⟪ Sem.⟦ Dʷ₁ v ⟧ ⟫ ᵀ)))
  (QM.mat-≐ (QI.≐-trans (QI.≐-sym (ᵀ-⊙ ⟪ Sem.⟦ Dʷ₁ v ⟧ ⟫ ⟪ Sem.⟦ Dʷ₁ u ⟧ ⟫))
                        (ᵀ-cong (QI.≐-sym (⟪∙⟫ Sem.⟦ Dʷ₁ u ⟧ Sem.⟦ Dʷ₁ v ⟧)))))))

------------------------------------------------------------------------
-- Equal matrices, equal readings

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

open O.Circuits Sem.val using (module Exact)

exact : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → ⟪ Sem.⟦ w ⟧ ⟫ QI.≐ ⟪ Sem.⟦ v ⟧ ⟫
exact {w = w} {v} (Exact.phased _ refl agree) x y =
  unscale hv hw (Eq.trans (Eq.sym L) (Eq.trans (Eq.cong φ (agree (digs x) (digs y))) R))
  where
  hw = proj₁ Sem.⟦ w ⟧
  hv = proj₁ Sem.⟦ v ⟧
  Fw = O.ix (proj₂ Sem.⟦ w ⟧) (digs x) (digs y)
  Fv = O.ix (proj₂ Sem.⟦ v ⟧) (digs x) (digs y)

  L : φ ((√2 O.^ hv) ZΩ.* Fw) ≡ (r QI.^ hv) * φ Fw
  L = Eq.trans (φ-* (√2 O.^ hv) Fw) (Eq.cong (_* φ Fw) (φ-^ √2 hv))

  R : φ (((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) ZΩ.* Fv) ≡ (r QI.^ hw) * φ Fv
  R = Eq.trans (φ-* ((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) Fv)
        (Eq.cong (_* φ Fv) (Eq.trans (φ-* (O.x O.^ 0) (√2 O.^ hw))
          (Eq.trans (Eq.cong₂ _*_ φ-1 (φ-^ √2 hw)) (*-identityˡ _))))
