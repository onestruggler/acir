------------------------------------------------------------------------
-- Presentations of groups
--
-- The phase of a one-wire circuit, as a triple.
--
-- Clifford.Qupit.SemRealises reduces `Realises` to sixteen equations in
-- ℤ/pℤ about the phase Φ, and ten of them are already discharged.  The
-- ones that are not — order-H, M-power, semi-MR, order-SH — all live on
-- the bottom wire and all need Φ COMPUTED rather than merely shown to
-- vanish.  This file is the calculus that computes it.
--
-- The observation.  Read in the Weyl model, a circuit on one wire is a
-- triple: a Pauli (x , z) on that wire, a 2×2 matrix (a b ; c d) — the
-- symplectic part, given by its action — and the phase φ.  Concatenation
-- multiplies these by the Heisenberg–Weyl law
--
--     (P , A , φ) · (Q , B , ψ)
--       = (P + A Q , A B , φ + ψ + ½·sform P (A Q)),
--
-- so a word is evaluated by folding that product over its letters, with
--
--     H = ((0,0) , (0 -1 ; 1 0) , 0)      S = ((0,σ) , (1 0 ; 1 1) , 0)
--
-- where σ = -½ is the Pauli that Simplified-V1's translation attaches to
-- S (SemShift.gate₁S-Pauli).  `Has w x z a b c d φ` is that reading of
-- w, stated as three equations, and `has-•` is the product law.  Nothing
-- here is specific to a rule: the whole of the remaining computation is
-- chains of `has-H·` and `has-S·`, the two left-multiplications.
--
-- Why a matrix and not a Symplectic.  The Symplectic record compares by
-- its action alone, so carrying the action as four coefficients loses
-- nothing and makes every step ordinary ring algebra in ℤ/pℤ — which is
-- what the ring solver wants.  `matmul` is the only place two matrices
-- ever meet.
--
-- What comes out.  Two things, and they settle four of the six:
--
--   * R = S · Z^½ has NO Pauli and NO phase (`has-R`): the Z-power
--     cancels S's own Pauli exactly, which is why Simplified-V1 states
--     everything over R.  Hence every word built from R-powers and H is
--     phase-free (`Free`), and the multiplier words M, XM are — so
--     order-H, M-power and semi-MR carry no correction;
--   * (S · H)³ has phase -½σ² (`has-SH3`), which is -⅛.  That is the one
--     rule whose phase is not zero, and it is exactly the exponent
--     Syntactics.corr assigns it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford.Qupit.SemLocal
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_)
import Relation.Binary.PropositionalEquality as Eq

open import Algebra.Properties.Ring (+-*-ring p-2)
  using ( -0#≈0# ; -‿+-comm ; -‿involutive ; -1*x≈-x
        ; -‿distribˡ-* ; -‿distribʳ-* ; [-x][-y]≈xy )
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
  using (mult ; mult-toℕ ; mult-p)

open import Word.Base using (Word ; ε ; _•_ ; _^_ ; [_]ʷ)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pIₙ ; sform ; sform1 ; _+ₚ_ ; +ₚ-identityˡ)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic)
open Symplectic using (ap)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  p-3 p-prime g* g-gen as Cli
import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS
import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem
import Examples.Groups.Clifford.Qupit.SemFE p-3 p-prime g* g-gen as FE
import Examples.Groups.Clifford.Qupit.SemShift p-3 p-prime g* g-gen as SH
import Examples.Groups.Clifford.Qupit.SemRealises p-3 p-prime g* g-gen as RL

------------------------------------------------------------------------
-- The two constants
--
-- h is the cocycle's coefficient and σ is the Pauli that S carries.  The
-- two are the SAME term up to a sign — Simplified-V1's -½ and
-- Semantics' ½ are both `((₂ , λ ()) ⁻¹) .proj₁`, so `σ ≡ - h` holds by
-- refl and the arithmetic below never has to compare two inverses.

h : ℤ ₚ
h = Sem.1/2

σ : ℤ ₚ
σ = Cli.-1/2

σ≡-h : σ ≡ - h
σ≡-h = Eq.refl

-- σ + h = 0 and σ + σ = -1: the only two facts about ½ that are used.
σ+h : σ + h ≡ ₀
σ+h = +-inverseˡ h

σ+σ : σ + σ ≡ - ₁
σ+σ = Eq.trans (-‿+-comm h h) (Eq.cong -_ Sem.half+half)

------------------------------------------------------------------------
-- Ring lemmas
--
-- Matrix multiplication (`matmul`, the only two-matrix step) by the ring
-- solver; everything else is small enough to spell out, and spelling it
-- out keeps the constants ₀ and ₁ out of the solver's expression
-- language.

matmul : ∀ (a b a' b' c' d' u v : ℤ ₚ) →
         a * (a' * u + b' * v) + b * (c' * u + d' * v)
           ≡ (a * a' + b * c') * u + (a * b' + b * d') * v
matmul = solve p-2 8
  (λ a b a' b' c' d' u v →
     ((a ⊗ (a' ⊗ u ⊕ b' ⊗ v)) ⊕ (b ⊗ (c' ⊗ u ⊕ d' ⊗ v))) ,
     ((((a ⊗ a') ⊕ (b ⊗ c')) ⊗ u) ⊕ (((a ⊗ b') ⊕ (b ⊗ d')) ⊗ v)))
  (λ {_} {_} {_} {_} {_} {_} {_} {_} → Eq.refl)

private
  -- ₁·x + ₀·y = x, ₀·x + ₁·y = y, ₀·x + (-₁)·y = -y, ₁·x + ₁·y = x + y.
  oz : ∀ (x y : ℤ ₚ) → ₁ * x + ₀ * y ≡ x
  oz x y = Eq.trans (Eq.cong₂ _+_ (*-identityˡ x) (*-zeroˡ y)) (+-identityʳ x)

  zo : ∀ (x y : ℤ ₚ) → ₀ * x + ₁ * y ≡ y
  zo x y = Eq.trans (Eq.cong₂ _+_ (*-zeroˡ x) (*-identityˡ y)) (+-identityˡ y)

  zm : ∀ (x y : ℤ ₚ) → ₀ * x + (- ₁) * y ≡ - y
  zm x y =
    Eq.trans (Eq.cong₂ _+_ (*-zeroˡ x) (-1*x≈-x y)) (+-identityˡ (- y))

  oo : ∀ (x y : ℤ ₚ) → ₁ * x + ₁ * y ≡ x + y
  oo x y = Eq.cong₂ _+_ (*-identityˡ x) (*-identityˡ y)

  -- -₀ · Y is ₀, so a sform whose left argument has no X-part collapses.
  negzero : ∀ (Y : ℤ ₚ) → (- ₀) * Y ≡ ₀
  negzero Y = Eq.trans (Eq.cong (_* Y) -0#≈0#) (*-zeroˡ Y)

  mm : (- ₁) * (- ₁) ≡ ₁
  mm = Eq.trans ([-x][-y]≈xy ₁ ₁) (*-identityˡ ₁)

------------------------------------------------------------------------
-- The calculus, at a fixed width
--
-- Everything is stated on the bottom wire of ₁₊ n wires: the Pauli is
-- (x , z) there and trivial above, and the action is the matrix there
-- and the identity above.

module Local (n : ℕ) where

  open RL.Width (₁₊ n) using (P⟦_⟧ ; S⟦_⟧ ; Φ ; Φ-gate ; Φ-ε ; Φ-• ; P-∙)

  ----------------------------------------------------------------------
  -- The two laws of the denotation that the calculus rests on
  --
  -- Both are Weyl's, restated: the action of a product is the composite
  -- (Width exports only the Pauli half, `P-∙`), and the phase of a
  -- product is the cocycle written out.

  S-∙ : (u v : QS.Circuit (₁₊ n)) (q : Pauli (₁₊ n)) →
        ap S⟦ u • v ⟧ q ≡ ap S⟦ u ⟧ (ap S⟦ v ⟧ q)
  S-∙ u v q = proj₂ (FE.Weyl.⟦⟧-∙ (₁₊ n) u v) q

  Φ-•' : (u v : QS.Circuit (₁₊ n)) →
         Φ (u • v) ≡ (Φ u + Φ v) + h * sform P⟦ u ⟧ (ap S⟦ u ⟧ P⟦ v ⟧)
  Φ-•' u v = Φ-• u v

  ----------------------------------------------------------------------
  -- The reading

  -- A RECORD, not the product it unfolds to.  Every step below infers
  -- the seven coefficients of its argument by unification, and a defined
  -- type is not injective: against `a * u + b * v ≡ ₀ * u + (- ₁) * v`
  -- Agda would go looking inside ℤ/pℤ's multiplication for a and b, and
  -- that unfolds mod-helper (measured: 426 s and unsolved metas).
  record Has (w : QS.Circuit (₁₊ n)) (x z a b c d φ : ℤ ₚ) : Set where
    constructor has
    field
      pauli : P⟦ w ⟧ ≡ (x , z) ∷ pIₙ
      act   : (u v : ℤ ₚ) (R : Pauli n) →
              ap S⟦ w ⟧ ((u , v) ∷ R) ≡ (a * u + b * v , c * u + d * v) ∷ R
      phase : Φ w ≡ φ

  -- Seven equations move a reading to an equal one.  This is where every
  -- normalisation happens: a `has-•` produces the raw product and this
  -- tidies it.
  has-≡ : ∀ {w x z a b c d φ x' z' a' b' c' d' φ'} →
          x ≡ x' → z ≡ z' → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → φ ≡ φ' →
          Has w x z a b c d φ → Has w x' z' a' b' c' d' φ'
  has-≡ Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl hw = hw

  ----------------------------------------------------------------------
  -- The product law

  has-• : ∀ {u v x z a b c d φ x' z' a' b' c' d' φ'} →
          Has u x z a b c d φ → Has v x' z' a' b' c' d' φ' →
          Has (u • v)
              (x + (a * x' + b * z')) (z + (c * x' + d * z'))
              (a * a' + b * c') (a * b' + b * d')
              (c * a' + d * c') (c * b' + d * d')
              ((φ + φ')
                + h * ((- x) * (c * x' + d * z') + (a * x' + b * z') * z))
  has-• {u} {v} {x} {z} {a} {b} {c} {d} {φ} {x'} {z'} {a'} {b'} {c'} {d'} {φ'}
        (has pu au fu) (has pv av fv) = has pe ae fe
    where
    q : Pauli1
    q = (a * x' + b * z' , c * x' + d * z')

    -- The right factor's Pauli, transported by the left one.
    apv : ap S⟦ u ⟧ P⟦ v ⟧ ≡ q ∷ pIₙ
    apv = Eq.trans (Eq.cong (ap S⟦ u ⟧) pv) (au x' z' pIₙ)

    pe : P⟦ u • v ⟧ ≡ (x + proj₁ q , z + proj₂ q) ∷ pIₙ
    pe = Eq.trans (P-∙ u v)
           (Eq.trans (Eq.cong₂ _+ₚ_ pu apv)
                     (Eq.cong ((x + proj₁ q , z + proj₂ q) ∷_)
                              (+ₚ-identityˡ pIₙ)))

    ae : (u' v' : ℤ ₚ) (R : Pauli n) →
         ap S⟦ u • v ⟧ ((u' , v') ∷ R)
           ≡ ((a * a' + b * c') * u' + (a * b' + b * d') * v'
             , (c * a' + d * c') * u' + (c * b' + d * d') * v') ∷ R
    ae u' v' R =
      Eq.trans (S-∙ u v ((u' , v') ∷ R))
        (Eq.trans (Eq.cong (ap S⟦ u ⟧) (av u' v' R))
          (Eq.trans (au (a' * u' + b' * v') (c' * u' + d' * v') R)
                    (Eq.cong (_∷ R)
                       (Eq.cong₂ _,_ (matmul a b a' b' c' d' u' v')
                                     (matmul c d a' b' c' d' u' v')))))

    sf : sform P⟦ u ⟧ (ap S⟦ u ⟧ P⟦ v ⟧)
           ≡ (- x) * proj₂ q + proj₁ q * z
    sf = Eq.trans (Eq.cong₂ sform pu apv)
           (Eq.trans (Eq.cong (sform1 (x , z) q +_)
                              (Sem.sform-pIˡ (pIₙ {n})))
                     (+-identityʳ (sform1 (x , z) q)))

    fe : Φ (u • v)
           ≡ (φ + φ') + h * ((- x) * proj₂ q + proj₁ q * z)
    fe = Eq.trans (Φ-•' u v)
           (Eq.cong₂ _+_ (Eq.cong₂ _+_ fu fv) (Eq.cong (h *_) sf))

  ----------------------------------------------------------------------
  -- The three atoms

  has-ε : Has ε ₀ ₀ ₁ ₀ ₀ ₁ ₀
  has-ε = has Eq.refl
              (λ u v R → Eq.cong (_∷ R)
                           (Eq.sym (Eq.cong₂ _,_ (oz u v) (zo u v))))
              Φ-ε

  has-H : Has (Pap.H {n}) ₀ ₀ ₀ (- ₁) ₁ ₀ ₀
  has-H = has Eq.refl
              (λ u v R → Eq.trans (SH.gate₁H-act u v R)
                           (Eq.cong (_∷ R)
                              (Eq.sym (Eq.cong₂ _,_ (zm u v) (oz u v)))))
              (Φ-gate _)

  has-S : Has (Pap.S {n}) ₀ σ ₁ ₀ ₁ ₁ ₀
  has-S = has SH.gate₁S-Pauli
              (λ u v R → Eq.trans (SH.gate₁S-act u v R)
                           (Eq.cong (_∷ R)
                              (Eq.sym (Eq.cong₂ _,_ (oz u v)
                                         (Eq.trans (oo u v) (+-comm u v))))))
              (Φ-gate _)

  ----------------------------------------------------------------------
  -- The two left-multiplications
  --
  -- Words are right-nested, so these — not right-multiplications — are
  -- what a chain is built from.  H moves the Pauli by a quarter turn and
  -- leaves the phase alone; S shears, adds its own σ, and contributes
  -- h·(x·σ) — which vanishes exactly when the accumulated Pauli has no
  -- X-part, and that is why Pauli-free blocks are phase-free.

  has-H· : ∀ {w x z a b c d φ} → Has w x z a b c d φ →
           Has (Pap.H • w) (- z) x (- c) (- d) a b φ
  has-H· {w} {x} {z} {a} {b} {c} {d} {φ} hw =
    has-≡ (Eq.trans (+-identityˡ _) (zm x z))
          (Eq.trans (+-identityˡ _) (oz x z))
          (zm a c) (zm b d) (oz a c) (oz b d)
          (Eq.trans (Eq.cong₂ _+_ (+-identityˡ φ)
                       (Eq.trans (Eq.cong (h *_)
                                    (Eq.trans (Eq.cong₂ _+_
                                                (negzero (₁ * x + ₀ * z))
                                                (*-zeroʳ (₀ * x + (- ₁) * z)))
                                              (+-identityʳ ₀)))
                                 (*-zeroʳ h)))
                    (+-identityʳ φ))
          (has-• has-H hw)

  has-S· : ∀ {w x z a b c d φ} → Has w x z a b c d φ →
           Has (Pap.S • w) x (σ + (x + z)) a b (a + c) (b + d)
               (φ + h * (x * σ))
  has-S· {w} {x} {z} {a} {b} {c} {d} {φ} hw =
    has-≡ (Eq.trans (+-identityˡ _) (oz x z))
          (Eq.cong (σ +_) (oo x z))
          (oz a c) (oz b d) (oo a c) (oo b d)
          (Eq.cong₂ _+_ (+-identityˡ φ)
             (Eq.cong (h *_)
                (Eq.trans (Eq.cong₂ _+_ (negzero (₁ * x + ₁ * z))
                                        (Eq.cong (_* σ) (oz x z)))
                          (+-identityˡ (x * σ)))))
          (has-• has-S hw)

  ----------------------------------------------------------------------
  -- Powers of S
  --
  -- S^k is the shear by k with the Pauli (0 , k·σ) and no phase: every
  -- step's cocycle term is h·(x·σ) with x = ₀.

  has-S^ : ∀ k → Has (Pap.S {n} ^ k) ₀ (mult k * σ) ₁ ₀ (mult k) ₁ ₀
  has-S^ zero =
    has-≡ Eq.refl (Eq.sym (*-zeroˡ σ)) Eq.refl Eq.refl Eq.refl Eq.refl
          Eq.refl has-ε
  has-S^ (₁₊ zero) =
    has-≡ Eq.refl
          (Eq.sym (Eq.trans (Eq.cong (_* σ) (+-identityʳ ₁)) (*-identityˡ σ)))
          Eq.refl Eq.refl (Eq.sym (+-identityʳ ₁)) Eq.refl Eq.refl has-S
  has-S^ (₂₊ k) =
    has-≡ Eq.refl
          (Eq.trans (Eq.cong (σ +_) (+-identityˡ (mult (₁₊ k) * σ)))
             (Eq.trans (Eq.cong (_+ (mult (₁₊ k) * σ))
                          (Eq.sym (*-identityˡ σ)))
                       (Eq.sym (*-distribʳ-+ σ ₁ (mult (₁₊ k))))))
          Eq.refl Eq.refl Eq.refl (+-identityˡ ₁)
          (Eq.trans (Eq.cong (₀ +_)
                       (Eq.trans (Eq.cong (h *_) (*-zeroˡ σ)) (*-zeroʳ h)))
                    (+-identityˡ ₀))
          (has-S· (has-S^ (₁₊ k)))

  -- ... in particular S ^ (p-1), whose exponent is -1.
  mult-p-1 : mult p-1 ≡ - ₁
  mult-p-1 =
    Eq.trans (Eq.sym (+-identityˡ (mult p-1)))
      (Eq.trans (Eq.cong (_+ mult p-1) (Eq.sym (+-inverseˡ ₁)))
        (Eq.trans (+-assoc (- ₁) ₁ (mult p-1))
                  (Eq.trans (Eq.cong ((- ₁) +_) mult-p) (+-identityʳ (- ₁)))))

  has-S⁻¹ : Has (Pap.S⁻¹ {n}) ₀ (- σ) ₁ ₀ (- ₁) ₁ ₀
  has-S⁻¹ =
    has-≡ Eq.refl
          (Eq.trans (Eq.cong (_* σ) mult-p-1) (-1*x≈-x σ))
          Eq.refl Eq.refl mult-p-1 Eq.refl Eq.refl (has-S^ p-1)

  ----------------------------------------------------------------------
  -- Z, X's partner
  --
  -- Z = H H S H H S⁻¹ has Pauli (0 , 1), acts trivially and carries no
  -- phase: five left-multiplications and the S-power above.

  private
    -- S⁻¹, then H, H, S, H, H — the word read from the right, each step
    -- tidied before the next so that no term ever grows.

    step1 : Has (Pap.H • Pap.S⁻¹ {n}) σ ₀ ₁ (- ₁) ₁ ₀ ₀
    step1 = has-≡ (-‿involutive σ) Eq.refl (-‿involutive ₁) Eq.refl
                  Eq.refl Eq.refl Eq.refl (has-H· has-S⁻¹)

    step2 : Has (Pap.H • Pap.H • Pap.S⁻¹ {n}) ₀ σ (- ₁) ₀ ₁ (- ₁) ₀
    step2 = has-≡ -0#≈0# Eq.refl Eq.refl -0#≈0# Eq.refl Eq.refl Eq.refl
                  (has-H· step1)

    step3 : Has (Pap.S • Pap.H • Pap.H • Pap.S⁻¹ {n})
                ₀ (- ₁) (- ₁) ₀ ₀ (- ₁) ₀
    step3 = has-≡ Eq.refl
                  (Eq.trans (Eq.cong (σ +_) (+-identityˡ σ)) σ+σ)
                  Eq.refl Eq.refl (+-inverseˡ ₁) (+-identityˡ (- ₁))
                  (Eq.trans (Eq.cong (₀ +_)
                               (Eq.trans (Eq.cong (h *_) (*-zeroˡ σ))
                                         (*-zeroʳ h)))
                            (+-identityˡ ₀))
                  (has-S· step2)

    step4 : Has (Pap.H • Pap.S • Pap.H • Pap.H • Pap.S⁻¹ {n})
                ₁ ₀ ₀ ₁ (- ₁) ₀ ₀
    step4 = has-≡ (-‿involutive ₁) Eq.refl -0#≈0# (-‿involutive ₁)
                  Eq.refl Eq.refl Eq.refl (has-H· step3)

  has-Z : Has (QS.CR.Z {n}) ₀ ₁ ₁ ₀ ₀ ₁ ₀
  has-Z = has-≡ -0#≈0# Eq.refl (-‿involutive ₁) -0#≈0# Eq.refl Eq.refl
                Eq.refl (has-H· step4)

  ----------------------------------------------------------------------
  -- ... and its powers

  has-Z· : ∀ {w x z a b c d φ} → Has w x z a b c d φ →
           Has (QS.CR.Z • w) x (₁ + z) a b c d (φ + h * x)
  has-Z· {w} {x} {z} {a} {b} {c} {d} {φ} hw =
    has-≡ (Eq.trans (+-identityˡ _) (oz x z))
          (Eq.cong (₁ +_) (zo x z))
          (oz a c) (oz b d) (zo a c) (zo b d)
          (Eq.cong₂ _+_ (+-identityˡ φ)
             (Eq.cong (h *_)
                (Eq.trans (Eq.cong₂ _+_ (negzero (₀ * x + ₁ * z))
                             (Eq.trans (*-identityʳ (₁ * x + ₀ * z))
                                       (oz x z)))
                          (+-identityˡ x))))
          (has-• has-Z hw)

  has-Z^ : ∀ k → Has (QS.CR.Z {n} ^ k) ₀ (mult k) ₁ ₀ ₀ ₁ ₀
  has-Z^ zero      = has-ε
  has-Z^ (₁₊ zero) =
    has-≡ Eq.refl (Eq.sym (+-identityʳ ₁)) Eq.refl Eq.refl Eq.refl Eq.refl
          Eq.refl has-Z
  has-Z^ (₂₊ k) =
    has-≡ Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
          (Eq.trans (Eq.cong (₀ +_) (*-zeroʳ h)) (+-identityˡ ₀))
          (has-Z· (has-Z^ (₁₊ k)))

  has-Z^' : ∀ (y : ℤ ₚ) → Has (QS.CR.Z^ y {n}) ₀ y ₁ ₀ ₀ ₁ ₀
  has-Z^' y =
    has-≡ Eq.refl (mult-toℕ y) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
          (has-Z^ (toℕ y))

  ----------------------------------------------------------------------
  -- R = S · Z^½, the phase-free shear
  --
  -- The Z-power's Pauli is (0 , ½) and S's is (0 , -½), so the two
  -- cancel: R has no Pauli at all, hence no phase, and it is the pure
  -- shear.  Everything the multiplier calculus is built from is a power
  -- of R, so everything the multiplier calculus is built from is free.

  has-R : Has (QS.CR.R {n}) ₀ ₀ ₁ ₀ ₁ ₁ ₀
  has-R =
    has-≡ Eq.refl (Eq.trans (Eq.cong (σ +_) (+-identityˡ h)) σ+h)
          Eq.refl Eq.refl (+-identityʳ ₁) (+-identityˡ ₁)
          (Eq.trans (Eq.cong (₀ +_)
                       (Eq.trans (Eq.cong (h *_) (*-zeroˡ σ)) (*-zeroʳ h)))
                    (+-identityˡ ₀))
          (has-S· (has-Z^' Pap.1/2))

  ----------------------------------------------------------------------
  -- Phase-free words
  --
  -- A word with no Pauli and no phase, whatever its matrix.  Closed
  -- under products, powers and the two constructors the multiplier words
  -- use, so `free-Φ` settles every rule both of whose sides are built
  -- from R-powers and H.

  Free : QS.Circuit (₁₊ n) → Set
  Free w = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → Has w ₀ ₀ a b c d ₀

  free-Φ : ∀ {w} → Free w → Φ w ≡ ₀
  free-Φ (_ , _ , _ , _ , hw) = Has.phase hw

  free-ε : Free ε
  free-ε = ₁ , ₀ , ₀ , ₁ , has-ε

  free-H : Free (Pap.H {n})
  free-H = ₀ , - ₁ , ₁ , ₀ , has-H

  free-R : Free (QS.CR.R {n})
  free-R = ₁ , ₀ , ₁ , ₁ , has-R

  free-• : ∀ {u v} → Free u → Free v → Free (u • v)
  free-• {u} {v} (a , b , c , d , hu) (a' , b' , c' , d' , hv) =
    _ , _ , _ , _ ,
    has-≡ (Eq.trans (+-identityˡ _)
             (Eq.trans (Eq.cong₂ _+_ (*-zeroʳ a) (*-zeroʳ b))
                       (+-identityʳ ₀)))
          (Eq.trans (+-identityˡ _)
             (Eq.trans (Eq.cong₂ _+_ (*-zeroʳ c) (*-zeroʳ d))
                       (+-identityʳ ₀)))
          Eq.refl Eq.refl Eq.refl Eq.refl
          (Eq.trans (Eq.cong₂ _+_ (+-identityˡ ₀)
                       (Eq.trans (Eq.cong (h *_)
                                    (Eq.trans (Eq.cong₂ _+_
                                                 (negzero (c * ₀ + d * ₀))
                                                 (*-zeroʳ (a * ₀ + b * ₀)))
                                              (+-identityʳ ₀)))
                                 (*-zeroʳ h)))
                    (+-identityʳ ₀))
          (has-• hu hv)

  free-^ : ∀ {w} → Free w → ∀ k → Free (w ^ k)
  free-^ fw zero      = free-ε
  free-^ fw (₁₊ zero) = fw
  free-^ fw (₂₊ k)    = free-• fw (free-^ fw (₁₊ k))

  free-R^ : ∀ (y : ℤ ₚ) → Free (QS.CR.R^ {n} y)
  free-R^ y = free-^ free-R (toℕ y)

  -- The multiplier shape, and the two ways of filling it.
  free-RHR : ∀ (y y' : ℤ ₚ) → Free (QS.CR.RHR {n} y y')
  free-RHR y y' =
    free-• (free-R^ y)
      (free-• free-H
        (free-• (free-R^ y')
          (free-• free-H (free-• (free-R^ y) free-H))))

  free-M : ∀ (y : ℤ* ₚ) → Free (QS.CR.M {n} y)
  free-M y = free-RHR (proj₁ y) (proj₁ (y ⁻¹))

  free-XM : ∀ (y : ℤ* ₚ) → Free (QS.CR.XM {n} y)
  free-XM y = free-RHR (proj₁ (y ⁻¹)) (proj₁ y)

  ----------------------------------------------------------------------
  -- (S · H)³ : the one rule with a phase
  --
  -- S · H is the reading ((0,σ) , (0 -1 ; 1 -1) , 0); squaring it moves
  -- the Pauli to (-σ , 0) and picks up -h·σ², and the third factor
  -- returns everything to the identity without adding anything more.

  has-SH : Has (Pap.S {n} • Pap.H) ₀ σ ₀ (- ₁) ₁ (- ₁) ₀
  has-SH =
    has-≡ Eq.refl
          (Eq.trans (Eq.cong (σ +_) (+-identityʳ ₀)) (+-identityʳ σ))
          Eq.refl Eq.refl (+-identityˡ ₁) (+-identityʳ (- ₁))
          (Eq.trans (Eq.cong (₀ +_)
                       (Eq.trans (Eq.cong (h *_) (*-zeroˡ σ)) (*-zeroʳ h)))
                    (+-identityˡ ₀))
          (has-S· has-H)

  has-SH3 : Has ((Pap.S {n} • Pap.H) ^ 3) ₀ ₀ ₁ ₀ ₀ ₁ (- (h * (σ * σ)))
  has-SH3 = has-≡ e1 e2 e3 e4 e5 e6 e7 (has-• has-SH sq)
    where
    -- (S·H)² , tidied.
    sq : Has ((Pap.S {n} • Pap.H) ^ 2) (- σ) ₀ (- ₁) ₁ (- ₁) ₀
                                       (- (h * (σ * σ)))
    sq = has-≡ sq1 sq2 sq3 sq4 sq5 sq6 sq7 (has-• has-SH has-SH)
      where
      sq1 : ₀ + (₀ * ₀ + (- ₁) * σ) ≡ - σ
      sq1 = Eq.trans (+-identityˡ _) (zm ₀ σ)

      sq2 : σ + (₁ * ₀ + (- ₁) * σ) ≡ ₀
      sq2 = Eq.trans (Eq.cong (σ +_)
                       (Eq.trans (Eq.cong₂ _+_ (*-zeroʳ ₁) (-1*x≈-x σ))
                                 (+-identityˡ (- σ))))
                     (+-inverseʳ σ)

      sq3 : ₀ * ₀ + (- ₁) * ₁ ≡ - ₁
      sq3 = Eq.trans (Eq.cong₂ _+_ (*-zeroˡ ₀) (*-identityʳ (- ₁)))
                     (+-identityˡ (- ₁))

      sq4 : ₀ * (- ₁) + (- ₁) * (- ₁) ≡ ₁
      sq4 = Eq.trans (Eq.cong₂ _+_ (*-zeroˡ (- ₁)) mm) (+-identityˡ ₁)

      sq5 : ₁ * ₀ + (- ₁) * ₁ ≡ - ₁
      sq5 = Eq.trans (Eq.cong₂ _+_ (*-zeroʳ ₁) (*-identityʳ (- ₁)))
                     (+-identityˡ (- ₁))

      sq6 : ₁ * (- ₁) + (- ₁) * (- ₁) ≡ ₀
      sq6 = Eq.trans (Eq.cong₂ _+_ (*-identityˡ (- ₁)) mm) (+-inverseˡ ₁)

      sqarg : ℤ ₚ
      sqarg = (- ₀) * (₁ * ₀ + (- ₁) * σ) + (₀ * ₀ + (- ₁) * σ) * σ

      sq7 : (₀ + ₀) + h * sqarg ≡ - (h * (σ * σ))
      sq7 = Eq.trans (Eq.cong (_+ h * sqarg) (+-identityʳ ₀))
              (Eq.trans (+-identityˡ (h * sqarg))
                (Eq.trans (Eq.cong (h *_)
                             (Eq.trans (Eq.cong₂ _+_
                                          (negzero (₁ * ₀ + (- ₁) * σ))
                                          (Eq.cong (_* σ) (zm ₀ σ)))
                               (Eq.trans (+-identityˡ ((- σ) * σ))
                                         (Eq.sym (-‿distribˡ-* σ σ)))))
                  (Eq.sym (-‿distribʳ-* h (σ * σ)))))

    e1 : ₀ + (₀ * (- σ) + (- ₁) * ₀) ≡ ₀
    e1 = Eq.trans (+-identityˡ _) (Eq.trans (zm (- σ) ₀) -0#≈0#)

    e2 : σ + (₁ * (- σ) + (- ₁) * ₀) ≡ ₀
    e2 = Eq.trans (Eq.cong (σ +_)
                    (Eq.trans (Eq.cong₂ _+_ (*-identityˡ (- σ)) (*-zeroʳ (- ₁)))
                              (+-identityʳ (- σ))))
                  (+-inverseʳ σ)

    e3 : ₀ * (- ₁) + (- ₁) * (- ₁) ≡ ₁
    e3 = Eq.trans (Eq.cong₂ _+_ (*-zeroˡ (- ₁)) mm) (+-identityˡ ₁)

    e4 : ₀ * ₁ + (- ₁) * ₀ ≡ ₀
    e4 = Eq.trans (Eq.cong₂ _+_ (*-zeroˡ ₁) (*-zeroʳ (- ₁)))
                  (+-identityʳ ₀)

    e5 : ₁ * (- ₁) + (- ₁) * (- ₁) ≡ ₀
    e5 = Eq.trans (Eq.cong₂ _+_ (*-identityˡ (- ₁)) mm) (+-inverseˡ ₁)

    e6 : ₁ * ₁ + (- ₁) * ₀ ≡ ₁
    e6 = Eq.trans (Eq.cong₂ _+_ (*-identityˡ ₁) (*-zeroʳ (- ₁)))
                  (+-identityʳ ₁)

    earg : ℤ ₚ
    earg = (- ₀) * (₁ * (- σ) + (- ₁) * ₀) + (₀ * (- σ) + (- ₁) * ₀) * σ

    e7 : (₀ + (- (h * (σ * σ)))) + h * earg ≡ - (h * (σ * σ))
    e7 = Eq.trans (Eq.cong (_+ h * earg) (+-identityˡ (- (h * (σ * σ)))))
           (Eq.trans (Eq.cong ((- (h * (σ * σ))) +_)
                        (Eq.trans (Eq.cong (h *_)
                                     (Eq.trans (Eq.cong₂ _+_
                                                  (negzero (₁ * (- σ) + (- ₁) * ₀))
                                                  (Eq.cong (_* σ)
                                                     (Eq.trans (zm (- σ) ₀)
                                                               -0#≈0#)))
                                       (Eq.trans (+-identityˡ (₀ * σ))
                                                 (*-zeroˡ σ))))
                                  (*-zeroʳ h)))
                     (+-identityʳ (- (h * (σ * σ)))))
