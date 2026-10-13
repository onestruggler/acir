------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂'s matrices against the source's on three qubits
--
-- Bian and Selinger's presentation of 3-qubit Clifford+CS operators
-- (Examples.Groups.Clifford+CS-3qubit) reads its words over iI, S0–S2,
-- K0–K2, CS01 and CS12 as 8 × 8 matrices over 𝔻[i] = ℤ[½, i], in
-- operator order, through the two-level generators of
-- Examples.Groups.Clifford+CS-TwoLevel.  CliffCS₂'s matrices are read
-- in 𝔻[ω] (⟪_⟫, from Clifford+T.Bridge), and 𝔻[i] maps into 𝔻[ω] by
-- ι (a + b i ↦ a + b ω², a ring map: ι-+, ι-*), so that ιM, entry by
-- entry, is a monoid map of matrices.  The decoding Dʷ reads their
-- words letter for letter (qubit k on wire k, K as ω⁷ H, iI as ω²):
-- every gate matrix is symmetric, so reading a word in diagram order
-- rather than operator order transposes its matrix, and bridge says
-- that ιM of their matrix of a word is the transpose of CliffCS₂'s
-- matrix of its decoding.  The generators are compared entry by entry
-- by evaluation, a decoded generator's power of ω set apart as a
-- scalar (entries): read as an operator product, ω⁷ H would cost 8⁷
-- terms an entry.
--
-- ω itself is not in 𝔻[i], which is why the encoding ℰ cannot send ω
-- anywhere and drops it (and turns H into K = ω† H): Completeness
-- restores the power of ω, whose parity two circuits with the same
-- matrix must share — ω times ι of anything is ι of nothing but 0 (par),
-- and a unitary matrix is not 0 (no-odd).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Bridge where

open import Algebra.Bundles using (CommutativeRing)
import Algebra.Properties.Ring as RingProps
open import Data.Empty using (⊥)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)
open import Quantum.Synthesis.Ring
  using (Dyadic ; _[ω] ; Omega ; Cplx ; SemiRingDyadic ; RingDyadic ; AdjointDyadic ; DecEqDyadic
        ; SemiRingCplx ; RingCplx ; AdjointCplx)
open import Quantum.Synthesis.Ring.Properties using (commutativeRing-𝔻)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; RingD ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; √½ ; module 𝔻R)
import Examples.Groups.Clifford+CS-TwoLevel.Ring as CR
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+CS-TwoLevel.Semantics as TLS
open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module CliffordCS)
import Examples.Groups.Clifford+CS-3qubit.Presentation as BS

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Sem
import Examples.Independence.Semantics.Qubit as O
open O using (module ZΩ ; √2)
open import Examples.Independence.Clifford.Ring using (φ ; φ-* ; φ-1 ; √½-√2)
open import Examples.Independence.Clifford+T.Bridge
  using (module QI ; module QM ; module MA ; digs ; Φ ; Φ-cong ; Φ-scal ; ⟪_⟫ ; ⟪∙⟫ ; ⟪ε⟫
        ; _ᵀ ; ᵀ-cong ; ᵀ-⊙ ; ᵀ-Id)

module CS = CliffordCS

private
  variable
    m n p : ℕ

------------------------------------------------------------------------
-- 𝔻[i] in 𝔻[ω]

-- The identities ι's laws come down to, over an abstract commutative
-- ring: stated over the dyadic fractions' own operations, a ring solver
-- would evaluate them on symbolic dyadics (whose record η unfolds every
-- product), and exhaust the heap.
private
  module Ids {c ℓ} (R : CommutativeRing c ℓ) where
    open CommutativeRing R renaming (refl to ≈-refl)
    open RingProps ring using (-0#≈0#)
    open import Relation.Binary.Reasoning.Setoid setoid

    z4 : ∀ {p q r s} → p ≈ 0# → q ≈ 0# → r ≈ 0# → s ≈ 0# → p + q + r + s ≈ 0#
    z4 e₁ e₂ e₃ e₄ = begin
      _                  ≈⟨ +-cong (+-cong (+-cong e₁ e₂) e₃) e₄ ⟩
      0# + 0# + 0# + 0#  ≈⟨ +-cong (+-cong (+-identityˡ 0#) ≈-refl) ≈-refl ⟩
      0# + 0# + 0#       ≈⟨ +-cong (+-identityˡ 0#) ≈-refl ⟩
      0# + 0#            ≈⟨ +-identityˡ 0# ⟩
      0#                 ∎

    n0 : ∀ {p} → p ≈ 0# → - p ≈ 0#
    n0 e = trans (-‿cong e) -0#≈0#

    idA : ∀ a b c d → 0# * c + b * 0# + 0# * d + a * 0# ≈ 0#
    idA a b c d = z4 (zeroˡ c) (zeroʳ b) (zeroˡ d) (zeroʳ a)

    idC : ∀ a b c d → 0# * c + a * 0# + - (0# * d) + - (b * 0#) ≈ 0#
    idC a b c d = z4 (zeroˡ c) (zeroʳ a) (n0 (zeroˡ d)) (n0 (zeroʳ b))

    idB : ∀ a b c d → b * c + 0# * 0# + a * d + - (0# * 0#) ≈ a * d + b * c
    idB a b c d = begin
      b * c + 0# * 0# + a * d + - (0# * 0#)
        ≈⟨ +-cong (+-cong (+-cong ≈-refl (zeroˡ 0#)) ≈-refl) (n0 (zeroˡ 0#)) ⟩
      b * c + 0# + a * d + 0#   ≈⟨ +-identityʳ _ ⟩
      b * c + 0# + a * d        ≈⟨ +-cong (+-identityʳ _) ≈-refl ⟩
      b * c + a * d             ≈⟨ +-comm _ _ ⟩
      a * d + b * c             ∎

    idD : ∀ a b c d → a * c + - (0# * 0#) + - (b * d) + - (0# * 0#) ≈ a * c + - (b * d)
    idD a b c d = begin
      a * c + - (0# * 0#) + - (b * d) + - (0# * 0#)
        ≈⟨ +-cong (+-cong (+-cong ≈-refl (n0 (zeroˡ 0#))) ≈-refl) (n0 (zeroˡ 0#)) ⟩
      a * c + 0# + - (b * d) + 0#   ≈⟨ +-identityʳ _ ⟩
      a * c + 0# + - (b * d)        ≈⟨ +-cong (+-identityʳ _) ≈-refl ⟩
      a * c + - (b * d)             ∎

    idP₁ : ∀ p q → 0# * p + 1# * 0# + 0# * q + - (0# * 0#) ≈ 0#
    idP₁ p q = z4 (zeroˡ p) (zeroʳ 1#) (zeroˡ q) (n0 (zeroˡ 0#))

    idP₂ : ∀ p q → 0# * p + - (0# * 0#) + - (0# * q) + - (1# * 0#) ≈ 0#
    idP₂ p q = z4 (zeroˡ p) (n0 (zeroˡ 0#)) (n0 (zeroˡ q)) (n0 (zeroʳ 1#))

  module I = Ids commutativeRing-𝔻

  cong₄ : ∀ {a a′ b b′ c c′ d d′ : Dyadic} → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
          Omega a b c d ≡ Omega a′ b′ c′ d′
  cong₄ refl refl refl refl = refl

open QI.AR using (_+_ ; _*_ ; 1# ; 0# ; *-identityˡ ; *-assoc ; *-comm)

-- a + b i ↦ b ω² + a.
ι : CR.D → D
ι (Cplx a b) = Omega 𝔻R.0# b 𝔻R.0# a

ι-inj : {x y : CR.D} → ι x ≡ ι y → x ≡ y
ι-inj {Cplx a b} {Cplx c d} e = Eq.cong₂ Cplx (Eq.cong _[ω].om-d e) (Eq.cong _[ω].om-b e)

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  ι-+ : (x y : CR.D) → ι (x CR.DR.+ y) ≡ ι x +ᴰ ι y
  ι-+ (Cplx a b) (Cplx c d) =
    Eq.cong₂ (λ u v → Omega u (b 𝔻R.+ d) v (a 𝔻R.+ c)) z z
    where
    z : 𝔻R.0# ≡ 𝔻R.0# 𝔻R.+ 𝔻R.0#
    z = Eq.sym (𝔻R.+-identityˡ 𝔻R.0#)

  ι-* : (x y : CR.D) → ι (x CR.DR.* y) ≡ ι x *ᴰ ι y
  ι-* (Cplx a b) (Cplx c d) =
    cong₄ (Eq.sym (I.idA a b c d)) (Eq.sym (I.idB a b c d))
          (Eq.sym (I.idC a b c d)) (Eq.sym (I.idD a b c d))

ι-sum : (f : Fin n → CR.D) → ι (TLS.sum f) ≡ MA.sum (ι ∘ f)
ι-sum {zero}  f = refl
ι-sum {suc n} f = Eq.trans (ι-+ (f zero) (TLS.sum (f ∘ suc)))
                           (Eq.cong (ι (f zero) +ᴰ_) (ι-sum (f ∘ suc)))

private
  ι-δ′ : (r c : Fin n) → Dec (r ≡ c) → ι (TLS.δ r c) ≡ MA.δ r c
  ι-δ′ r .r (yes refl) = Eq.trans (Eq.cong ι (TLS.δ-refl r)) (Eq.sym (MA.δ-refl r))
  ι-δ′ r c  (no r≢c)   = Eq.trans (Eq.cong ι (TLS.δ-≢ r≢c)) (Eq.sym (MA.δ-≢ r≢c))

-- (Through the δ lemmas: a with on r ≟ c here exhausts the heap.)
ι-δ : (r c : Fin n) → ι (TLS.δ r c) ≡ MA.δ r c
ι-δ r c = ι-δ′ r c (r FinP.≟ c)

------------------------------------------------------------------------
-- Matrices over 𝔻[i] in 𝔻[ω]

-- The product over 𝔻[ω], its instance given: EucDomain's own instance
-- for 𝔻[ω] is in scope through the qualified imports.
infixl 7 _·ᴰ_
_·ᴰ_ : Matrix m n D → Matrix n p D → Matrix m p D
_·ᴰ_ = _·*·_ {{RingD}}

ιM : Matrix m n CR.D → Matrix m n D
ιM M = MA.mk (λ r c → ι (TLS.ent M r c))

ent-ιM : (M : Matrix m n CR.D) (r : Fin m) (c : Fin n) → MA.ent (ιM M) r c ≡ ι (TLS.ent M r c)
ent-ιM M = MA.ent-mk (λ r c → ι (TLS.ent M r c))

ιM-·*· : (M : Matrix m n CR.D) (N : Matrix n p CR.D) → ιM (M ·*· N) ≡ ιM M ·ᴰ ιM N
ιM-·*· M N = MA.mat-ext λ r c → begin
  MA.ent (ιM (M ·*· N)) r c                                    ≡⟨ ent-ιM (M ·*· N) r c ⟩
  ι (TLS.ent (M ·*· N) r c)                                    ≡⟨ Eq.cong ι (TLS.ent-·*· M N r c) ⟩
  ι (TLS.sum (λ k → TLS.ent M r k CR.DR.* TLS.ent N k c))     ≡⟨ ι-sum (λ k → TLS.ent M r k CR.DR.* TLS.ent N k c) ⟩
  MA.sum (λ k → ι (TLS.ent M r k CR.DR.* TLS.ent N k c))      ≡⟨ MA.sum-cong-≗ (λ k → ι-* (TLS.ent M r k) (TLS.ent N k c)) ⟩
  MA.sum (λ k → ι (TLS.ent M r k) *ᴰ ι (TLS.ent N k c))       ≡⟨ MA.sum-cong-≗ (λ k →
                     Eq.cong₂ _*ᴰ_ (Eq.sym (ent-ιM M r k)) (Eq.sym (ent-ιM N k c))) ⟩
  MA.sum (λ k → MA.ent (ιM M) r k *ᴰ MA.ent (ιM N) k c)      ≡⟨ Eq.sym (MA.ent-·*· (ιM M) (ιM N) r c) ⟩
  MA.ent (ιM M ·ᴰ ιM N) r c                                    ∎
  where open Eq.≡-Reasoning

ιM-𝕀 : ιM (TLS.𝕀 {n}) ≡ MA.𝕀
ιM-𝕀 = MA.mat-ext λ r c →
  Eq.trans (ent-ιM TLS.𝕀 r c)
  (Eq.trans (Eq.cong ι (TLS.ent-𝕀 r c)) (Eq.trans (ι-δ r c) (Eq.sym (MA.ent-𝕀 r c))))

ιM-inj : {M N : Matrix m n CR.D} → ιM M ≡ ιM N → M ≡ N
ιM-inj {M = M} {N} e = TLS.mat-ext λ r c →
  ι-inj (Eq.trans (Eq.sym (ent-ιM M r c))
        (Eq.trans (Eq.cong (λ X → MA.ent X r c) e) (ent-ιM N r c)))

------------------------------------------------------------------------
-- The matrix of a two-level word

-- The product of its generators' matrices.
gm : Word (TL.Gen m) → Matrix m m CR.D
gm [ g ]ʷ  = TLS.gmat g
gm ε       = TLS.𝕀
gm (u • v) = gm u ·*· gm v

⟦⟧≡gm : (u : Word (TL.Gen m)) → TLS.⟦ u ⟧ᵐ ≡ gm u
⟦⟧≡gm [ g ]ʷ  = TLS.⟦g⟧ᵐ≡ g
⟦⟧≡gm ε       = refl
⟦⟧≡gm (u • v) = Eq.trans (TLS.⟦•⟧ᵐ u v) (Eq.cong₂ _·*·_ (⟦⟧≡gm u) (⟦⟧≡gm v))

------------------------------------------------------------------------
-- Powers of ω

ωs : ℕ → Circuit n
ωs zero    = ε
ωs (suc k) = ω • ωs k

-- ω read in 𝔻[ω].
ωᴰ : D
ωᴰ = φ O.x

⟪ω⟫ : ⟪ Sem.⟦ ω {n} ⟧ ⟫ QI.≐ QI.scal ωᴰ
⟪ω⟫ {n} = QI.≐-trans (QI.scale-1 _) (QI.≐-trans (Φ-cong (O.ix-scalM {n} O.x)) (Φ-scal O.x))

⟪ωs⟫ : (k : ℕ) → ⟪ Sem.⟦ ωs {n} k ⟧ ⟫ QI.≐ QI.scal (ωᴰ QI.^ k)
⟪ωs⟫ zero    = QI.≐-trans ⟪ε⟫ (QI.≐-sym QI.scal-1)
⟪ωs⟫ {n} (suc k) =
  QI.≐-trans (⟪∙⟫ Sem.⟦ ω {n} ⟧ Sem.⟦ ωs k ⟧)
  (QI.≐-trans (QI.⊙-cong (⟪ωs⟫ k) ⟪ω⟫)
  (QI.≐-trans (QI.scal-⊙ (ωᴰ QI.^ k) ωᴰ)
              (λ x y → Eq.cong (λ c → QI.scal c x y) (*-comm (ωᴰ QI.^ k) ωᴰ))))

-- A circuit after a power of ω: its reading, scaled.
⟪ωs•⟫ : (k : ℕ) (u : Circuit n) →
        ⟪ Sem.⟦ ωs k • u ⟧ ⟫ QI.≐ QI.scale (ωᴰ QI.^ k) ⟪ Sem.⟦ u ⟧ ⟫
⟪ωs•⟫ k u =
  QI.≐-trans (⟪∙⟫ Sem.⟦ ωs k ⟧ Sem.⟦ u ⟧)
  (QI.≐-trans (QI.⊙-cong (QI.≐-refl ⟪ Sem.⟦ u ⟧ ⟫) (⟪ωs⟫ k))
              (QI.scal-⊙ʳ (ωᴰ QI.^ k) ⟪ Sem.⟦ u ⟧ ⟫))

⟪ω•⟫ : (u : Circuit n) → ⟪ Sem.⟦ ω • u ⟧ ⟫ QI.≐ QI.scale ωᴰ ⟪ Sem.⟦ u ⟧ ⟫
⟪ω•⟫ u =
  QI.≐-trans (⟪∙⟫ Sem.⟦ ω ⟧ Sem.⟦ u ⟧)
  (QI.≐-trans (QI.⊙-cong (QI.≐-refl ⟪ Sem.⟦ u ⟧ ⟫) ⟪ω⟫) (QI.scal-⊙ʳ ωᴰ ⟪ Sem.⟦ u ⟧ ⟫))

------------------------------------------------------------------------
-- Three wires: the encoding, and their words decoded

-- Their swap: (K ⊗ K) CZ three times, and i³ for the phase.
SW01 SW12 : Word CS.Gen
SW01 = (CS.K0 • CS.K1 • CS.CS01 • CS.CS01) • (CS.K0 • CS.K1 • CS.CS01 • CS.CS01)
     • (CS.K0 • CS.K1 • CS.CS01 • CS.CS01) • CS.iI • CS.iI • CS.iI
SW12 = (CS.K1 • CS.K2 • CS.CS12 • CS.CS12) • (CS.K1 • CS.K2 • CS.CS12 • CS.CS12)
     • (CS.K1 • CS.K2 • CS.CS12 • CS.CS12) • CS.iI • CS.iI • CS.iI

-- ω is dropped and H becomes K = ω† H: what is lost is counted by
-- Completeness.
ℰ : Gen 3 → Word CS.Gen
ℰ (gate₀ ⌈ ω-gate ⌉)          = ε
ℰ (gate₁ ⌈ H-gate ⌉)          = CS.K0
ℰ (gate₁ ⌈ S-gate ⌉)          = CS.S0
ℰ (gate₂ ⌈ CS-gate ⌉)         = CS.CS01
ℰ (gate₂ swap)                = SW01
ℰ (gate₀ ⌈ ω-gate ⌉ ↥)        = ε
ℰ (gate₁ ⌈ H-gate ⌉ ↥)        = CS.K1
ℰ (gate₁ ⌈ S-gate ⌉ ↥)        = CS.S1
ℰ (gate₂ ⌈ CS-gate ⌉ ↥)       = CS.CS12
ℰ (gate₂ swap ↥)              = SW12
ℰ ((gate₀ ⌈ ω-gate ⌉ ↥) ↥)    = ε
ℰ ((gate₁ ⌈ H-gate ⌉ ↥) ↥)    = CS.K2
ℰ ((gate₁ ⌈ S-gate ⌉ ↥) ↥)    = CS.S2
ℰ (((gate₀ ⌈ ω-gate ⌉ ↥) ↥) ↥) = ε

ℰʷ : Circuit 3 → Word CS.Gen
ℰʷ [ g ]ʷ  = ℰ g
ℰʷ ε       = ε
ℰʷ (w • v) = ℰʷ w • ℰʷ v

-- A generator of theirs decoded: a power of ω (sc) and a gate (G).
sc : CS.Gen → ℕ
sc CS.iI-gen = 2
sc CS.K0-gen = 7
sc CS.K1-gen = 7
sc CS.K2-gen = 7
sc _         = 0

G : CS.Gen → Circuit 3
G CS.S0-gen   = S
G CS.S1-gen   = S ↑
G CS.S2-gen   = S ↑ ↑
G CS.CS01-gen = CS
G CS.CS12-gen = CS ↑
G CS.iI-gen   = ε
G CS.K0-gen   = H
G CS.K1-gen   = H ↑
G CS.K2-gen   = H ↑ ↑

D₀ : CS.Gen → Circuit 3
D₀ x = ωs (sc x) • G x

-- A word of theirs, letter for letter.
Dʷ : Word CS.Gen → Circuit 3
Dʷ [ g ]ʷ  = D₀ g
Dʷ ε       = ε
Dʷ (w • v) = Dʷ w • Dʷ v

-- Their generators, entry by entry.
opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  entries : (x : CS.Gen) (r c : Fin 8) →
            MA.ent (ιM (gm (BS.tl x))) r c ≡
            (ωᴰ QI.^ sc x) * MA.ent (QM.mat (⟪ Sem.⟦ G x ⟧ ⟫ ᵀ)) r c
  entries CS.S0-gen zero zero = refl
  entries CS.S0-gen zero (suc zero) = refl
  entries CS.S0-gen zero (suc (suc zero)) = refl
  entries CS.S0-gen zero (suc (suc (suc zero))) = refl
  entries CS.S0-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S0-gen (suc zero) zero = refl
  entries CS.S0-gen (suc zero) (suc zero) = refl
  entries CS.S0-gen (suc zero) (suc (suc zero)) = refl
  entries CS.S0-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.S0-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S0-gen (suc (suc zero)) zero = refl
  entries CS.S0-gen (suc (suc zero)) (suc zero) = refl
  entries CS.S0-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.S0-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.S0-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S0-gen (suc (suc (suc zero))) zero = refl
  entries CS.S0-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.S0-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.S0-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.S0-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen zero zero = refl
  entries CS.S1-gen zero (suc zero) = refl
  entries CS.S1-gen zero (suc (suc zero)) = refl
  entries CS.S1-gen zero (suc (suc (suc zero))) = refl
  entries CS.S1-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen (suc zero) zero = refl
  entries CS.S1-gen (suc zero) (suc zero) = refl
  entries CS.S1-gen (suc zero) (suc (suc zero)) = refl
  entries CS.S1-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.S1-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen (suc (suc zero)) zero = refl
  entries CS.S1-gen (suc (suc zero)) (suc zero) = refl
  entries CS.S1-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.S1-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.S1-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen (suc (suc (suc zero))) zero = refl
  entries CS.S1-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.S1-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.S1-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.S1-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen zero zero = refl
  entries CS.S2-gen zero (suc zero) = refl
  entries CS.S2-gen zero (suc (suc zero)) = refl
  entries CS.S2-gen zero (suc (suc (suc zero))) = refl
  entries CS.S2-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen (suc zero) zero = refl
  entries CS.S2-gen (suc zero) (suc zero) = refl
  entries CS.S2-gen (suc zero) (suc (suc zero)) = refl
  entries CS.S2-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.S2-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen (suc (suc zero)) zero = refl
  entries CS.S2-gen (suc (suc zero)) (suc zero) = refl
  entries CS.S2-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.S2-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.S2-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen (suc (suc (suc zero))) zero = refl
  entries CS.S2-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.S2-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.S2-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.S2-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.S2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen zero zero = refl
  entries CS.CS01-gen zero (suc zero) = refl
  entries CS.CS01-gen zero (suc (suc zero)) = refl
  entries CS.CS01-gen zero (suc (suc (suc zero))) = refl
  entries CS.CS01-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen (suc zero) zero = refl
  entries CS.CS01-gen (suc zero) (suc zero) = refl
  entries CS.CS01-gen (suc zero) (suc (suc zero)) = refl
  entries CS.CS01-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.CS01-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen (suc (suc zero)) zero = refl
  entries CS.CS01-gen (suc (suc zero)) (suc zero) = refl
  entries CS.CS01-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.CS01-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.CS01-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen (suc (suc (suc zero))) zero = refl
  entries CS.CS01-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.CS01-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.CS01-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.CS01-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS01-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen zero zero = refl
  entries CS.CS12-gen zero (suc zero) = refl
  entries CS.CS12-gen zero (suc (suc zero)) = refl
  entries CS.CS12-gen zero (suc (suc (suc zero))) = refl
  entries CS.CS12-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen (suc zero) zero = refl
  entries CS.CS12-gen (suc zero) (suc zero) = refl
  entries CS.CS12-gen (suc zero) (suc (suc zero)) = refl
  entries CS.CS12-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.CS12-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen (suc (suc zero)) zero = refl
  entries CS.CS12-gen (suc (suc zero)) (suc zero) = refl
  entries CS.CS12-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.CS12-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.CS12-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen (suc (suc (suc zero))) zero = refl
  entries CS.CS12-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.CS12-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.CS12-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.CS12-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.CS12-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen zero zero = refl
  entries CS.iI-gen zero (suc zero) = refl
  entries CS.iI-gen zero (suc (suc zero)) = refl
  entries CS.iI-gen zero (suc (suc (suc zero))) = refl
  entries CS.iI-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen (suc zero) zero = refl
  entries CS.iI-gen (suc zero) (suc zero) = refl
  entries CS.iI-gen (suc zero) (suc (suc zero)) = refl
  entries CS.iI-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.iI-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen (suc (suc zero)) zero = refl
  entries CS.iI-gen (suc (suc zero)) (suc zero) = refl
  entries CS.iI-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.iI-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.iI-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen (suc (suc (suc zero))) zero = refl
  entries CS.iI-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.iI-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.iI-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.iI-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.iI-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen zero zero = refl
  entries CS.K0-gen zero (suc zero) = refl
  entries CS.K0-gen zero (suc (suc zero)) = refl
  entries CS.K0-gen zero (suc (suc (suc zero))) = refl
  entries CS.K0-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen (suc zero) zero = refl
  entries CS.K0-gen (suc zero) (suc zero) = refl
  entries CS.K0-gen (suc zero) (suc (suc zero)) = refl
  entries CS.K0-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.K0-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen (suc (suc zero)) zero = refl
  entries CS.K0-gen (suc (suc zero)) (suc zero) = refl
  entries CS.K0-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.K0-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.K0-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen (suc (suc (suc zero))) zero = refl
  entries CS.K0-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.K0-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.K0-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.K0-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K0-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen zero zero = refl
  entries CS.K1-gen zero (suc zero) = refl
  entries CS.K1-gen zero (suc (suc zero)) = refl
  entries CS.K1-gen zero (suc (suc (suc zero))) = refl
  entries CS.K1-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen (suc zero) zero = refl
  entries CS.K1-gen (suc zero) (suc zero) = refl
  entries CS.K1-gen (suc zero) (suc (suc zero)) = refl
  entries CS.K1-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.K1-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen (suc (suc zero)) zero = refl
  entries CS.K1-gen (suc (suc zero)) (suc zero) = refl
  entries CS.K1-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.K1-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.K1-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen (suc (suc (suc zero))) zero = refl
  entries CS.K1-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.K1-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.K1-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.K1-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K1-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen zero zero = refl
  entries CS.K2-gen zero (suc zero) = refl
  entries CS.K2-gen zero (suc (suc zero)) = refl
  entries CS.K2-gen zero (suc (suc (suc zero))) = refl
  entries CS.K2-gen zero (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen zero (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen zero (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen zero (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen (suc zero) zero = refl
  entries CS.K2-gen (suc zero) (suc zero) = refl
  entries CS.K2-gen (suc zero) (suc (suc zero)) = refl
  entries CS.K2-gen (suc zero) (suc (suc (suc zero))) = refl
  entries CS.K2-gen (suc zero) (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen (suc (suc zero)) zero = refl
  entries CS.K2-gen (suc (suc zero)) (suc zero) = refl
  entries CS.K2-gen (suc (suc zero)) (suc (suc zero)) = refl
  entries CS.K2-gen (suc (suc zero)) (suc (suc (suc zero))) = refl
  entries CS.K2-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen (suc (suc (suc zero))) zero = refl
  entries CS.K2-gen (suc (suc (suc zero))) (suc zero) = refl
  entries CS.K2-gen (suc (suc (suc zero))) (suc (suc zero)) = refl
  entries CS.K2-gen (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
  entries CS.K2-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) zero = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) (suc zero) = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) zero = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) zero = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) zero = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) = refl
  entries CS.K2-gen (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl

bridge-gen : (x : CS.Gen) → ιM (gm (BS.tl x)) ≡ QM.mat (⟪ Sem.⟦ D₀ x ⟧ ⟫ ᵀ)
bridge-gen x = MA.mat-ext λ r c →
  Eq.trans (entries x r c)
  (Eq.sym (Eq.trans (QM.ent-mat (⟪ Sem.⟦ D₀ x ⟧ ⟫ ᵀ) r c)
          (Eq.trans (⟪ωs•⟫ (sc x) (G x) (QM.bits 3 c) (QM.bits 3 r))
                    (Eq.cong ((ωᴰ QI.^ sc x) *_) (Eq.sym (QM.ent-mat (⟪ Sem.⟦ G x ⟧ ⟫ ᵀ) r c))))))

-- ι of their matrix of any word is the transpose of CliffCS₂'s matrix
-- of its decoding.
bridge : (u : Word CS.Gen) → ιM (proj₁ BS.⟦ u ⟧) ≡ QM.mat (⟪ Sem.⟦ Dʷ u ⟧ ⟫ ᵀ)
bridge [ x ]ʷ  = Eq.trans (Eq.cong ιM (⟦⟧≡gm (BS.tl x))) (bridge-gen x)
bridge ε       = Eq.trans ιM-𝕀
  (Eq.sym (Eq.trans (QM.mat-≐ {n = 3} (QI.≐-trans (ᵀ-cong ⟪ε⟫) ᵀ-Id)) (QM.mat-Id {n = 3})))
bridge (u • v) =
  Eq.trans (Eq.cong ιM (TLS.⟦•⟧ᵐ ((BS.tl ʷ) u) ((BS.tl ʷ) v)))
  (Eq.trans (ιM-·*· (proj₁ BS.⟦ u ⟧) (proj₁ BS.⟦ v ⟧))
  (Eq.trans (Eq.cong₂ _·ᴰ_ (bridge u) (bridge v))
  (Eq.trans (Eq.sym (QM.mat-⊙ (⟪ Sem.⟦ Dʷ u ⟧ ⟫ ᵀ) (⟪ Sem.⟦ Dʷ v ⟧ ⟫ ᵀ)))
  (QM.mat-≐ (QI.≐-trans (QI.≐-sym (ᵀ-⊙ ⟪ Sem.⟦ Dʷ v ⟧ ⟫ ⟪ Sem.⟦ Dʷ u ⟧ ⟫))
                        (ᵀ-cong (QI.≐-sym (⟪∙⟫ Sem.⟦ Dʷ u ⟧ Sem.⟦ Dʷ v ⟧))))))))

-- Words whose decodings read alike have the same matrix.
same : (a b : Word CS.Gen) → ⟪ Sem.⟦ Dʷ a ⟧ ⟫ QI.≐ ⟪ Sem.⟦ Dʷ b ⟧ ⟫ →
       proj₁ BS.⟦ a ⟧ ≡ proj₁ BS.⟦ b ⟧
same a b e = ιM-inj (Eq.trans (bridge a) (Eq.trans (QM.mat-≐ (ᵀ-cong e)) (Eq.sym (bridge b))))

------------------------------------------------------------------------
-- ω is not in 𝔻[i]

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  ωᴰ≡ : ωᴰ ≡ Omega 𝔻R.0# 𝔻R.0# 𝔻R.1# 𝔻R.0#
  ωᴰ≡ = refl

  -- ω (p + q i) = q ω³ + p ω, which is ι of something only when it is 0.
  par : (x y : CR.D) → ι x ≡ ωᴰ *ᴰ ι y → x ≡ CR.DR.0#
  par (Cplx a b) (Cplx p q) e = Eq.cong₂ Cplx
    (Eq.trans (Eq.cong _[ω].om-d e′) (I.idP₂ p q))
    (Eq.trans (Eq.cong _[ω].om-b e′) (I.idP₁ p q))
    where
    e′ : ι (Cplx a b) ≡ Omega 𝔻R.0# 𝔻R.0# 𝔻R.1# 𝔻R.0# *ᴰ ι (Cplx p q)
    e′ = Eq.trans e (Eq.cong (_*ᴰ ι (Cplx p q)) ωᴰ≡)

-- A unitary matrix has an entry that is not 0.  (Every argument is
-- given: inferred, Agda unifies through symbolic dyadic arithmetic.)
private
  col0 : (P Q : Matrix (suc n) (suc n) CR.D) → (∀ k → TLS.ent Q k zero ≡ CR.DR.0#) →
         TLS.ent (P ·*· Q) zero zero ≡ CR.DR.0#
  col0 P Q z = Eq.trans (TLS.ent-·*· P Q zero zero)
    (TLS.sum-zero (λ k → TLS.ent P zero k CR.DR.* TLS.ent Q k zero)
                  (λ k → Eq.trans (Eq.cong (TLS.ent P zero k CR.DR.*_) (z k))
                                  (CR.DR.zeroʳ (TLS.ent P zero k))))

  0≢1 : CR.DR.0# ≡ CR.DR.1# → ⊥
  0≢1 ()

nonzero : (A : Matrix (suc n) (suc n) CR.D) → TLS.Unitary A →
          (∀ r c → TLS.ent A r c ≡ CR.DR.0#) → ⊥
nonzero {n} A (u , _) z = 0≢1
  (Eq.trans (Eq.sym (col0 (adjoint A) A (λ k → z k zero)))
  (Eq.trans (Eq.cong (λ M → TLS.ent M zero zero) u)
  (Eq.trans (TLS.ent-𝕀 {suc n} zero zero) (TLS.δ-refl {suc n} zero))))

-- So ω times their matrix of a word is never ι of another's.
no-odd : (a b : Word CS.Gen) → ⟪ Sem.⟦ Dʷ a ⟧ ⟫ QI.≐ ⟪ Sem.⟦ ω • Dʷ b ⟧ ⟫ → ⊥
no-odd a b e = nonzero Ma (proj₂ BS.⟦ a ⟧) zeros
  where
  Ma Mb : Matrix 8 8 CR.D
  Ma = proj₁ BS.⟦ a ⟧
  Mb = proj₁ BS.⟦ b ⟧
  Ra Rb : QI.Op 3
  Ra = ⟪ Sem.⟦ Dʷ a ⟧ ⟫
  Rb = ⟪ Sem.⟦ Dʷ b ⟧ ⟫

  zeros : ∀ r c → TLS.ent Ma r c ≡ CR.DR.0#
  zeros r c = par (TLS.ent Ma r c) (TLS.ent Mb r c) (begin
    ι (TLS.ent Ma r c)                              ≡⟨ Eq.sym (ent-ιM Ma r c) ⟩
    MA.ent (ιM Ma) r c                              ≡⟨ Eq.cong (λ X → MA.ent X r c) (bridge a) ⟩
    MA.ent (QM.mat (Ra ᵀ)) r c                     ≡⟨ QM.ent-mat (Ra ᵀ) r c ⟩
    Ra (QM.bits 3 c) (QM.bits 3 r)                 ≡⟨ e (QM.bits 3 c) (QM.bits 3 r) ⟩
    ⟪ Sem.⟦ ω • Dʷ b ⟧ ⟫ (QM.bits 3 c) (QM.bits 3 r) ≡⟨ ⟪ω•⟫ (Dʷ b) (QM.bits 3 c) (QM.bits 3 r) ⟩
    ωᴰ * Rb (QM.bits 3 c) (QM.bits 3 r)            ≡⟨ Eq.cong (ωᴰ *_) (Eq.sym (QM.ent-mat (Rb ᵀ) r c)) ⟩
    ωᴰ * MA.ent (QM.mat (Rb ᵀ)) r c                ≡⟨ Eq.cong (λ X → ωᴰ * MA.ent X r c) (Eq.sym (bridge b)) ⟩
    ωᴰ * MA.ent (ιM Mb) r c                         ≡⟨ Eq.cong (ωᴰ *_) (ent-ιM Mb r c) ⟩
    ωᴰ *ᴰ ι (TLS.ent Mb r c)                        ∎)
    where open Eq.≡-Reasoning

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
