------------------------------------------------------------------------
-- Presentations of groups
--
-- The M-word action on DEGENERATE cosets (inj₁ ml'), COSET half: the
-- inj₁ mirror of SrelWDM.ractM!.  The width-1 action of ZM x is
-- (e , (α , β)) ↦ (e , (x·α , x⁻¹·β)) with e UNCHANGED — the ZM word's
-- total S-emission is zero on every branch — so at inj₁ the M column
-- returns to mm and only the A box moves.  Each branch threads the six
-- ZM segments (three S-power blocks, three H steps) with the block
-- engines of PushWD and closes the M column by the weighted chain
-- helper blockH-0 (a block at exponent j and an H at exponent jH with
-- nsum t j + jH ≡ 0 cancel).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿involutive ; -‿distribʳ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM
  p-2 p-prime using (nsum-neg)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using
  (itf ; mbSⁿm ; mbSⁿ-shiftζ ; mbSⁿ-block ; module MbS-OP ;
   ζΔ ; _⊞_ ; ⊞-⊞ ; ζΔ-+ ; ⊞-ζ0 ; nsum-*)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWD
  p-2 p-prime using
  (inj₁-a-eq ; kS0 ; kS0-val ; sqInv ; kHn ; kHn-val ; inv-val-cong ;
   ract-S^-inj₁-0b-coset ; ract-S^-inj₁-a+-coset)

------------------------------------------------------------------------
-- Weighted closure: an S-power block at exponent j followed by a step
-- at exponent jH cancels on the M column when nsum t j + jH ≡ 0.

blockH-0 : ∀ {k} (j jH : ℤ ₚ) (t : ℕ) (mm : M (₁₊ k)) (bv : Vec B k) →
  nsum t j + jH ≡ ₀ →
  mbSⁿm (toℕ jH) (itf (λ z → mbSⁿm (toℕ j) z bv) t mm) bv ≡ mm
blockH-0 {k} j jH t mm bv w0 =
  Eq.trans (Eq.cong (λ z → mbSⁿm (toℕ jH) z bv) (mbSⁿ-block j t mm bv))
  (Eq.trans (mbSⁿ-shiftζ jH (mm ⊞ ζΔ (nsum t j) σm) bv)
  (Eq.trans (Eq.cong ((mm ⊞ ζΔ (nsum t j) σm) ⊞_)
      (Eq.cong (ζΔ jH) (MbS-OP.σ-const bv mm (ζΔ (nsum t j) σm))))
  (Eq.trans (⊞-⊞ mm (ζΔ (nsum t j) σm) (ζΔ jH σm))
  (Eq.trans (Eq.cong (mm ⊞_) (ζΔ-+ (nsum t j) jH σm))
  (Eq.trans (Eq.cong (λ z → mm ⊞ ζΔ z σm) w0)
            (⊞-ζ0 mm σm))))))
  where
  σm = MbS-OP.σ bv mm

------------------------------------------------------------------------
-- The (₀ , ₁₊ β') branch of the inj₁ M-word action.
--
-- Orbit (mirroring SrelWDM.ractM-0b): the first S^ x block emits
-- x·β⁻² into the cascade with the box fixed; H turns the box to
-- (β , 0); S^ x⁻¹ shifts it to (β , ₁₊ u) [= (β , −x⁻¹β)] with no
-- emission; H emits kHn β' u = −x·β⁻² (the cancelling partner) and
-- turns the box to (u , −β); S^ x closes the b-component to 0; the
-- final H parks the box at (₀ , x⁻¹β).  Total cascade weight 0, so
-- the M column returns to mm.

module RactM-0b {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (x* : ℤ* ₚ) (β' : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ β') ≢ (₀ , ₀))
  (u : Fin (₁₊ p-2)) (eq-u : - ((x* ⁻¹) .proj₁ * ₁₊ β') ≡ ₁₊ u)
  (nz' : (₀ , (x* ⁻¹) .proj₁ * ₁₊ β') ≢ (₀ , ₀))
  where

  private
    x  = x* .proj₁
    ix = (x* ⁻¹) .proj₁
    β  = ₁₊ β'
    β* : ℤ* ₚ
    β* = (₁₊ β' , λ ())
    instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    mm₁ = itf (λ z → mbSⁿm (toℕ (kS0 {m} β' nz)) z bv) (toℕ x) mm
    mm₂ = Φ (kHn {m} β' u (λ ())) mm₁

    -- kHn β' u is the negated block weight (SrelWDM.Kfix's chain).
    Q : (((x* ⁻¹) *' (β* *' β*)) ⁻¹) .proj₁ ≡ x * sqInv β'
    Q = Eq.trans (inv-distrib (x* ⁻¹) (β* *' β*))
        (Eq.cong₂ _*_ (inv-involutive x*) (inv-distrib β* β*))

    KH0 : kHn {m} β' u (λ ()) ≡ - (x * sqInv β')
    KH0 = Eq.trans (kHn-val {m} β' u (λ ()))
      (Eq.trans (inv-val-cong (β* *' (₁₊ u , λ ()))
          (-' ((x* ⁻¹) *' (β* *' β*)))
          (Eq.trans (Eq.cong (β *_) (Eq.sym eq-u))
          (Eq.trans (Eq.sym (-‿distribʳ-* β (ix * β)))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc β ix β))
              (Eq.trans (Eq.cong (_* β) (*-comm β ix))
                        (*-assoc ix β β)))))))
      (Eq.trans (inv-neg-comm ((x* ⁻¹) *' (β* *' β*))) (Eq.cong -_ Q)))

    w0 : nsum (toℕ x) (kS0 {m} β' nz) + kHn {m} β' u (λ ()) ≡ ₀
    w0 = Eq.trans (Eq.cong₂ _+_
        (Eq.trans (Eq.cong (nsum (toℕ x)) (kS0-val {m} β' nz))
                  (nsum-* x (sqInv β')))
        KH0)
      (+-inverseʳ (x * sqInv β'))

    M-return : mm₂ ≡ mm
    M-return = blockH-0 (kS0 {m} β' nz) (kHn {m} β' u (λ ()))
                 (toℕ x) mm bv w0

    -- x · ₁₊ u ≡ − β (SrelWDM's xu≡-β).
    xu≡-β : x * ₁₊ u ≡ - β
    xu≡-β = Eq.trans (Eq.cong (x *_) (Eq.sym eq-u))
      (Eq.trans (Eq.sym (-‿distribʳ-* x (ix * β)))
      (Eq.cong -_
        (Eq.trans (Eq.sym (*-assoc x ix β))
        (Eq.trans (Eq.cong (_* β) (lemma-⁻¹ʳ x {{instᵢ}}))
                  (*-identityˡ β)))))

    val5 : - β + nsum (toℕ x) (- ₁₊ u) ≡ ₀
    val5 = Eq.trans (Eq.cong (- β +_)
        (Eq.trans (nsum-neg x (₁₊ u))
          (Eq.trans (Eq.cong -_ xu≡-β) (-‿involutive β))))
      (+-inverseˡ β)

    ab-eq : _≡_ {A = ℤ ₚ × ℤ ₚ} (₀ , - ₁₊ u) (₀ , ix * β)
    ab-eq = Eq.cong (λ z → (₀ , z))
      (Eq.trans (Eq.cong -_ (Eq.sym eq-u)) (-‿involutive (ix * β)))

    c₀ c₁ c₂ c₃ c₄ c₅ cF : C (₂₊ m)
    c₀ = inj₁ (mm  , (bv , ((₀ , β) , nz)))
    c₁ = inj₁ (mm₁ , (bv , ((₀ , β) , nz)))
    c₂ = inj₁ (mm₁ , (bv , ((₁₊ β' , ₀) , λ ())))
    c₃ = inj₁ (mm₁ , (bv , ((₁₊ β' , ₁₊ u) , λ ())))
    c₄ = inj₁ (mm₂ , (bv , ((₁₊ u , - β) , λ ())))
    c₅ = inj₁ (mm₂ , (bv , ((₁₊ u , ₀) , λ ())))
    cF = inj₁ (mm  , (bv , ((₀ , ix * β) , nz')))

    seg₁ : ((ract {₁₊ m} ᵗ) c₀ (S^ x)) .proj₂ ≡ c₁
    seg₁ = ract-S^-inj₁-0b-coset mm bv β' nz (toℕ x)

    seg₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    seg₂ = inj₁-a-eq Eq.refl

    seg₃ : ((ract {₁₊ m} ᵗ) c₂ (S^ ix)) .proj₂ ≡ c₃
    seg₃ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm₁) (proj₂ mm₁) bv β' ₀ (λ ())
        (toℕ ix))
      (inj₁-a-eq (Eq.cong (₁₊ β' ,_)
        (Eq.trans (+-identityˡ (nsum (toℕ ix) (- β)))
          (Eq.trans (nsum-neg ix β) eq-u))))

    seg₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    seg₄ = inj₁-a-eq Eq.refl

    seg₅ : ((ract {₁₊ m} ᵗ) c₄ (S^ x)) .proj₂ ≡ c₅
    seg₅ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm₂) (proj₂ mm₂) bv u (- β) (λ ())
        (toℕ x))
      (inj₁-a-eq (Eq.cong (₁₊ u ,_) val5))

    seg₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate)) ≡ cF
    seg₆ = Eq.trans (inj₁-a-eq ab-eq)
      (Eq.cong (λ zz → inj₁ (zz , (bv , ((₀ , ix * β) , nz'))))
        M-return)

  ractM-inj₁-0b :
    ((ract {₁₊ m} ᵗ) c₀ (ZM x*)) .proj₂ ≡ cF
  ractM-inj₁-0b =
    Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c
        (H • (S^ ix • (H • (S^ x • H))))) .proj₂) seg₁)
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c
        (S^ ix • (H • (S^ x • H)))) .proj₂) seg₂)
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c
        (H • (S^ x • H))) .proj₂) seg₃)
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c
        (S^ x • H)) .proj₂) seg₄)
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c H) .proj₂) seg₅)
              seg₆))))
