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
open import Data.Empty using (⊥-elim)
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
  using (-‿involutive ; -‿distribʳ-* ; -‿distribˡ-* ; -‿+-comm ; -0#≈0#)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as TDw
  using ()
import Examples.Groups.Symplectic.BR.Two.L2-CZ p-2 p-prime as LCZ2
open import Examples.Groups.Symplectic.Normalization.Pushing.DS
  p-2 p-prime using (d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1
  p-2 p-prime using (A-dir-S-power)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM
  p-2 p-prime using (nsum-neg ; valM-C ; valM-D ; Mact-nz)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using
  (itf ; mbSⁿm ; mbSⁿ-shiftζ ; mbSⁿ-block ; module MbS-OP ;
   ζΔ ; _⊞_ ; ⊞-⊞ ; ζΔ-+ ; ⊞-ζ0 ; nsum-* ; chainΦ ; chain-0 ; sumZ ;
   +-swap ; eCZ)
open import Data.List using () renaming ([] to []ᴸ ; _∷_ to _∷ᴸ_)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWD
  p-2 p-prime using
  (inj₁-a-eq ; kS0 ; kS0-val ; sqInv ; kHn ; kHn-val ; inv-val-cong ;
   ract-S^-inj₁-0b-coset ; ract-S^-inj₁-a+-coset ; ract-S-inj₁-a+ ;
   orderS-inj₁-0b-coset ; orderS-inj₁-a+ ;
   orderH-inj₁-0b ; orderH-inj₁-a0 ; module OrderH-nn ;
   module OrderSH-0b ; module OrderSH-a0 ;
   module OrderSH-nn0 ; module OrderSH-nnw ;
   module CommHHS-0b ; module CommHHS-a0 ;
   module CommHHS-nn0 ; module CommHHS-nnw)

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

-- The mirror: a step at jH followed by a block at j.
Hblock-0 : ∀ {k} (jH j : ℤ ₚ) (t : ℕ) (mm : M (₁₊ k)) (bv : Vec B k) →
  jH + nsum t j ≡ ₀ →
  itf (λ z → mbSⁿm (toℕ j) z bv) t (mbSⁿm (toℕ jH) mm bv) ≡ mm
Hblock-0 {k} jH j t mm bv w0 =
  Eq.trans (Eq.cong (itf (λ z → mbSⁿm (toℕ j) z bv) t)
      (mbSⁿ-shiftζ jH mm bv))
  (Eq.trans (mbSⁿ-block j t (mm ⊞ ζΔ jH σm) bv)
  (Eq.trans (Eq.cong ((mm ⊞ ζΔ jH σm) ⊞_)
      (Eq.cong (ζΔ (nsum t j)) (MbS-OP.σ-const bv mm (ζΔ jH σm))))
  (Eq.trans (⊞-⊞ mm (ζΔ jH σm) (ζΔ (nsum t j) σm))
  (Eq.trans (Eq.cong (mm ⊞_) (ζΔ-+ jH (nsum t j) σm))
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

------------------------------------------------------------------------
-- The (₁₊ α' , β) branch with β − xα ≡ 0 (mirror of SrelWDM.ractM-w0).

module RactM-w0 {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (x* : ℤ* ₚ) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀)) (y g : Fin (₁₊ p-2))
  (Xeq0 : β + - (x* .proj₁ * ₁₊ α') ≡ ₀)
  (eq-y : - ₁₊ α' ≡ ₁₊ y)
  (eq-g : β ≡ ₁₊ g)
  (nz' : (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) ≢ (₀ , ₀))
  where

  private
    x  = x* .proj₁
    ix = (x* ⁻¹) .proj₁
    instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}
    iα = ((₁₊ α' , λ ()) ⁻¹) .proj₁
    V  = ix * (iα * iα)

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    mmB = itf (λ z → mbSⁿm (toℕ (kS0 {m} y (λ ()))) z bv) (toℕ ix) mm

    beq : β ≡ x * ₁₊ α'
    beq = +-‿cancel β (x * ₁₊ α') Xeq0

    xy≡-β : x * ₁₊ y ≡ - β
    xy≡-β = Eq.trans (Eq.cong (x *_) (Eq.sym eq-y))
      (Eq.trans (Eq.sym (-‿distribʳ-* x (₁₊ α')))
                (Eq.cong -_ (Eq.sym beq)))

    ixβ≡α : ix * β ≡ ₁₊ α'
    ixβ≡α = Eq.trans (Eq.cong (ix *_) beq)
      (Eq.trans (Eq.sym (*-assoc ix x (₁₊ α')))
      (Eq.trans (Eq.cong (_* ₁₊ α') (lemma-⁻¹ˡ x {{instᵢ}}))
                (*-identityˡ (₁₊ α'))))

    ab-eq : _≡_ {A = ℤ ₚ × ℤ ₚ} (₁₊ g , - ₁₊ y) (x * ₁₊ α' , ix * β)
    ab-eq = Eq.cong₂ _,_ (Eq.trans (Eq.sym eq-g) beq)
      (Eq.trans
        (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ α')))
        (Eq.sym ixβ≡α))

    iy-eq : ((₁₊ y , λ ()) ⁻¹) .proj₁ ≡ - iα
    iy-eq = Eq.trans
      (inv-cong (₁₊ y , λ ()) (-' (₁₊ α' , λ ())) (Eq.sym eq-y))
      (inv-neg-comm (₁₊ α' , λ ()))

    w1V : nsum (toℕ ix) (kS0 {m} y (λ ())) ≡ V
    w1V = Eq.trans (Eq.cong (nsum (toℕ ix)) (kS0-val {m} y (λ ())))
      (Eq.trans (nsum-* ix (sqInv y))
        (Eq.cong (ix *_)
          (Eq.trans (Eq.cong₂ _*_ iy-eq iy-eq) (negneg-* iα iα))))

    αxα : ₁₊ α' * (x * ₁₊ α') ≡ x * (₁₊ α' * ₁₊ α')
    αxα = Eq.trans (Eq.sym (*-assoc (₁₊ α') x (₁₊ α')))
      (Eq.trans (Eq.cong (_* ₁₊ α') (*-comm (₁₊ α') x))
                (*-assoc x (₁₊ α') (₁₊ α')))

    KHyg : kHn {m} y g (λ ()) ≡ - V
    KHyg = Eq.trans (kHn-val {m} y g (λ ()))
      (KabV x* α' y g
        (Eq.trans (Eq.cong₂ _*_ (Eq.sym eq-y) (Eq.sym eq-g))
        (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ α') β))
          (Eq.cong -_ (Eq.trans (Eq.cong (₁₊ α' *_) beq) αxα)))))

    w0-sum : nsum (toℕ ix) (kS0 {m} y (λ ())) + kHn {m} y g (λ ()) ≡ ₀
    w0-sum = Eq.trans (Eq.cong₂ _+_ w1V KHyg) (+-inverseʳ V)

    M-return : Φ (kHn {m} y g (λ ())) mmB ≡ mm
    M-return = blockH-0 (kS0 {m} y (λ ())) (kHn {m} y g (λ ()))
                 (toℕ ix) mm bv w0-sum

    c₀ c₁ c₂ c₃ c₄ c₅ cF : C (₂₊ m)
    c₀ = inj₁ (mm  , (bv , ((₁₊ α' , β) , nz)))
    c₁ = inj₁ (mm  , (bv , ((₁₊ α' , ₀) , λ ())))
    c₂ = inj₁ (mm  , (bv , ((₀ , ₁₊ y) , λ ())))
    c₃ = inj₁ (mmB , (bv , ((₀ , ₁₊ y) , λ ())))
    c₄ = inj₁ (mmB , (bv , ((₁₊ y , ₀) , λ ())))
    c₅ = inj₁ (mmB , (bv , ((₁₊ y , ₁₊ g) , λ ())))
    cF = inj₁ (mm  , (bv , ((x * ₁₊ α' , ix * β) , nz')))

    seg₁ : ((ract {₁₊ m} ᵗ) c₀ (S^ x)) .proj₂ ≡ c₁
    seg₁ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm) (proj₂ mm) bv α' β nz (toℕ x))
      (inj₁-a-eq (Eq.cong (₁₊ α' ,_)
        (Eq.trans (Eq.cong (β +_) (nsum-neg x (₁₊ α'))) Xeq0)))

    seg₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    seg₂ = inj₁-a-eq (Eq.cong (λ z → (₀ , z)) eq-y)

    seg₃ : ((ract {₁₊ m} ᵗ) c₂ (S^ ix)) .proj₂ ≡ c₃
    seg₃ = ract-S^-inj₁-0b-coset mm bv y (λ ()) (toℕ ix)

    seg₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    seg₄ = inj₁-a-eq Eq.refl

    seg₅ : ((ract {₁₊ m} ᵗ) c₄ (S^ x)) .proj₂ ≡ c₅
    seg₅ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mmB) (proj₂ mmB) bv y ₀ (λ ())
        (toℕ x))
      (inj₁-a-eq (Eq.cong (₁₊ y ,_)
        (Eq.trans (+-0ˡ (nsum (toℕ x) (- ₁₊ y)))
        (Eq.trans (nsum-neg x (₁₊ y))
        (Eq.trans (Eq.cong -_ xy≡-β)
          (Eq.trans (-‿involutive β) eq-g))))))

    seg₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate)) ≡ cF
    seg₆ = Eq.trans (inj₁-a-eq ab-eq)
      (Eq.cong
        (λ zz → inj₁ (zz , (bv , ((x * ₁₊ α' , ix * β) , nz'))))
        M-return)

  ractM-inj₁-w0 :
    ((ract {₁₊ m} ᵗ) c₀ (ZM x*)) .proj₂ ≡ cF
  ractM-inj₁-w0 =
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

------------------------------------------------------------------------
-- The (₁₊ α' , β) branch with β ≡ 0 (mirror of SrelWDM.ractM-b0).

module RactM-b0 {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (x* : ℤ* ₚ) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀)) (w t : Fin (₁₊ p-2))
  (Xeq : β + - (x* .proj₁ * ₁₊ α') ≡ ₁₊ w)
  (eq-b0 : β ≡ ₀)
  (eq-t : - ₁₊ w ≡ ₁₊ t)
  (nz' : (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) ≢ (₀ , ₀))
  where

  private
    x  = x* .proj₁
    ix = (x* ⁻¹) .proj₁
    instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}
    iα = ((₁₊ α' , λ ()) ⁻¹) .proj₁
    V  = ix * (iα * iα)

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    mm₁ = Φ (kHn {m} α' w (λ ())) mm
    mmB = itf (λ z → mbSⁿm (toℕ (kS0 {m} t (λ ()))) z bv) (toℕ x) mm₁

    t≡xα : ₁₊ t ≡ x * ₁₊ α'
    t≡xα = Eq.trans (Eq.sym eq-t)
      (Eq.trans (Eq.cong -_ (Eq.sym Xeq))
      (Eq.trans (Eq.cong -_ (Eq.cong (_+ - (x * ₁₊ α')) eq-b0))
      (Eq.trans (Eq.cong -_ (+-0ˡ (- (x * ₁₊ α'))))
                (-‿involutive (x * ₁₊ α')))))

    ab-eq : _≡_ {A = ℤ ₚ × ℤ ₚ} (₁₊ t , ₀) (x * ₁₊ α' , ix * β)
    ab-eq = Eq.cong₂ _,_ t≡xα
      (Eq.sym (Eq.trans (Eq.cong (ix *_) eq-b0) (*-zeroʳ ix)))

    it-eq : ((₁₊ t , λ ()) ⁻¹) .proj₁ ≡ ix * iα
    it-eq = Eq.trans
      (inv-cong (₁₊ t , λ ()) (x* *' (₁₊ α' , λ ())) t≡xα)
      (inv-distrib x* (₁₊ α' , λ ()))

    wBV : nsum (toℕ x) (kS0 {m} t (λ ())) ≡ V
    wBV = Eq.trans (Eq.cong (nsum (toℕ x)) (kS0-val {m} t (λ ())))
      (Eq.trans (nsum-* x (sqInv t))
      (Eq.trans (Eq.cong (x *_) (Eq.cong₂ _*_ it-eq it-eq))
      (Eq.trans (Eq.sym (*-assoc x (ix * iα) (ix * iα)))
      (Eq.trans (Eq.cong (_* (ix * iα))
        (Eq.trans (Eq.sym (*-assoc x ix iα))
        (Eq.trans (Eq.cong (_* iα) (lemma-⁻¹ʳ x {{instᵢ}}))
                  (*-identityˡ iα))))
      (Eq.trans (Eq.sym (*-assoc iα ix iα))
      (Eq.trans (Eq.cong (_* iα) (*-comm iα ix))
                (*-assoc ix iα iα)))))))

    αxα : ₁₊ α' * (x * ₁₊ α') ≡ x * (₁₊ α' * ₁₊ α')
    αxα = Eq.trans (Eq.sym (*-assoc (₁₊ α') x (₁₊ α')))
      (Eq.trans (Eq.cong (_* ₁₊ α') (*-comm (₁₊ α') x))
                (*-assoc x (₁₊ α') (₁₊ α')))

    KHαw : kHn {m} α' w (λ ()) ≡ - V
    KHαw = Eq.trans (kHn-val {m} α' w (λ ()))
      (KabV x* α' α' w
        (Eq.trans (Eq.cong (₁₊ α' *_)
          (Eq.trans (Eq.sym Xeq)
          (Eq.trans (Eq.cong (_+ - (x * ₁₊ α')) eq-b0)
                    (+-0ˡ (- (x * ₁₊ α'))))))
        (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ α') (x * ₁₊ α')))
                  (Eq.cong -_ αxα))))

    w0-sum : kHn {m} α' w (λ ()) + nsum (toℕ x) (kS0 {m} t (λ ())) ≡ ₀
    w0-sum = Eq.trans (Eq.cong₂ _+_ KHαw wBV) (+-inverseˡ V)

    M-return : mmB ≡ mm
    M-return = Hblock-0 (kHn {m} α' w (λ ())) (kS0 {m} t (λ ()))
                 (toℕ x) mm bv w0-sum

    c₀ c₁ c₂ c₃ c₄ c₅ cF : C (₂₊ m)
    c₀ = inj₁ (mm  , (bv , ((₁₊ α' , β) , nz)))
    c₁ = inj₁ (mm  , (bv , ((₁₊ α' , ₁₊ w) , λ ())))
    c₂ = inj₁ (mm₁ , (bv , ((₁₊ w , - ₁₊ α') , λ ())))
    c₃ = inj₁ (mm₁ , (bv , ((₁₊ w , ₀) , λ ())))
    c₄ = inj₁ (mm₁ , (bv , ((₀ , ₁₊ t) , λ ())))
    c₅ = inj₁ (mmB , (bv , ((₀ , ₁₊ t) , λ ())))
    cF = inj₁ (mm  , (bv , ((x * ₁₊ α' , ix * β) , nz')))

    seg₁ : ((ract {₁₊ m} ᵗ) c₀ (S^ x)) .proj₂ ≡ c₁
    seg₁ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm) (proj₂ mm) bv α' β nz (toℕ x))
      (inj₁-a-eq (Eq.cong (₁₊ α' ,_)
        (Eq.trans (Eq.cong (β +_) (nsum-neg x (₁₊ α'))) Xeq)))

    seg₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    seg₂ = inj₁-a-eq Eq.refl

    seg₃ : ((ract {₁₊ m} ᵗ) c₂ (S^ ix)) .proj₂ ≡ c₃
    seg₃ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm₁) (proj₂ mm₁) bv w (- ₁₊ α')
        (λ ()) (toℕ ix))
      (inj₁-a-eq (Eq.cong (₁₊ w ,_)
        (Eq.trans (Eq.cong ((- ₁₊ α') +_) (nsum-neg ix (₁₊ w)))
        (Eq.trans (Eq.cong (λ z → - ₁₊ α' + - (ix * z)) (Eq.sym Xeq))
        (Eq.trans (valM-C x* (₁₊ α') β)
        (Eq.trans (Eq.cong (λ z → - (ix * z)) eq-b0)
          (Eq.trans (Eq.cong -_ (*-zeroʳ ix)) -0#≈0#)))))))

    seg₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    seg₄ = inj₁-a-eq (Eq.cong (λ z → (₀ , z)) eq-t)

    seg₅ : ((ract {₁₊ m} ᵗ) c₄ (S^ x)) .proj₂ ≡ c₅
    seg₅ = ract-S^-inj₁-0b-coset mm₁ bv t (λ ()) (toℕ x)

    seg₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate)) ≡ cF
    seg₆ = Eq.trans (inj₁-a-eq ab-eq)
      (Eq.cong
        (λ zz → inj₁ (zz , (bv , ((x * ₁₊ α' , ix * β) , nz'))))
        M-return)

  ractM-inj₁-b0 :
    ((ract {₁₊ m} ᵗ) c₀ (ZM x*)) .proj₂ ≡ cF
  ractM-inj₁-b0 =
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

------------------------------------------------------------------------
-- The generic branch: α ≠ 0, β ≠ 0, β − xα ≠ 0 (mirror of
-- SrelWDM.ractM-nn).  Three fully nonzero H-stops; the exponents
-- telescope by the x-scaled partial fraction (pf-invx).

module RactM-nn {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (x* : ℤ* ₚ) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀)) (w v s g : Fin (₁₊ p-2))
  (Xeq : β + - (x* .proj₁ * ₁₊ α') ≡ ₁₊ w)
  (eq-v : - ((x* ⁻¹) .proj₁ * β) ≡ ₁₊ v)
  (eq-s : x* .proj₁ * ₁₊ α' ≡ ₁₊ s)
  (eq-g : β ≡ ₁₊ g)
  (nz' : (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) ≢ (₀ , ₀))
  where

  private
    x  = x* .proj₁
    ix = (x* ⁻¹) .proj₁
    instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    j₁ = kHn {m} α' w (λ ())
    j₂ = kHn {m} w v (λ ())
    j₃ = kHn {m} v s (λ ())

    mm₁ = Φ j₁ mm
    mm₂ = Φ j₂ mm₁

    I1 : Kab w v ≡ - (x * Kab w g)
    I1 = Eq.trans
      (inv-cong ((₁₊ w , λ ()) *' (₁₊ v , λ ()))
                (-' ((x* ⁻¹) *' ((₁₊ w , λ ()) *' (₁₊ g , λ ()))))
        (Eq.trans (Eq.cong (₁₊ w *_) (Eq.sym eq-v))
        (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ w) (ix * β)))
        (Eq.cong -_
          (Eq.trans (Eq.sym (*-assoc (₁₊ w) ix β))
          (Eq.trans (Eq.cong (_* β) (*-comm (₁₊ w) ix))
          (Eq.trans (*-assoc ix (₁₊ w) β)
                    (Eq.cong (λ z → ix * (₁₊ w * z)) eq-g))))))))
      (Eq.trans
        (inv-neg-comm ((x* ⁻¹) *' ((₁₊ w , λ ()) *' (₁₊ g , λ ()))))
        (Eq.cong -_
          (Eq.trans (inv-distrib (x* ⁻¹) ((₁₊ w , λ ()) *' (₁₊ g , λ ())))
                    (Eq.cong (_* Kab w g) (inv-involutive x*)))))

    I2 : Kab v s ≡ - Kab α' g
    I2 = Eq.trans
      (inv-cong ((₁₊ v , λ ()) *' (₁₊ s , λ ()))
                (-' ((₁₊ α' , λ ()) *' (₁₊ g , λ ())))
        (Eq.trans (Eq.cong₂ _*_ (Eq.sym eq-v) (Eq.sym eq-s))
        (Eq.trans (Eq.sym (-‿distribˡ-* (ix * β) (x * ₁₊ α')))
        (Eq.cong -_
          (Eq.trans (*-assoc ix β (x * ₁₊ α'))
          (Eq.trans (Eq.cong (ix *_)
            (Eq.trans (Eq.sym (*-assoc β x (₁₊ α')))
            (Eq.trans (Eq.cong (_* ₁₊ α') (*-comm β x))
                      (*-assoc x β (₁₊ α')))))
          (Eq.trans (Eq.sym (*-assoc ix x (β * ₁₊ α')))
          (Eq.trans (Eq.cong (_* (β * ₁₊ α')) (lemma-⁻¹ˡ x {{instᵢ}}))
          (Eq.trans (*-identityˡ (β * ₁₊ α'))
          (Eq.trans (*-comm β (₁₊ α'))
                    (Eq.cong (₁₊ α' *_) eq-g)))))))))))
      (inv-neg-comm ((₁₊ α' , λ ()) *' (₁₊ g , λ ())))

    awb-g : x * ₁₊ α' + ₁₊ w ≡ ₁₊ g
    awb-g = Eq.trans (Eq.cong (x * ₁₊ α' +_) (Eq.sym Xeq))
      (Eq.trans (+-comm (x * ₁₊ α') (β + - (x * ₁₊ α')))
      (Eq.trans (+-assoc β (- (x * ₁₊ α')) (x * ₁₊ α'))
      (Eq.trans (Eq.cong (β +_) (+-inverseˡ (x * ₁₊ α')))
      (Eq.trans (+-identityʳ β) eq-g))))

    sum0 : sumZ (j₁ ∷ᴸ j₂ ∷ᴸ j₃ ∷ᴸ []ᴸ) ≡ ₀
    sum0 =
      Eq.trans (Eq.cong₂ _+_ (kHn-val {m} α' w (λ ()))
        (Eq.cong₂ _+_ (Eq.trans (kHn-val {m} w v (λ ())) I1)
          (Eq.cong₂ _+_ (Eq.trans (kHn-val {m} v s (λ ())) I2) Eq.refl)))
      (Eq.trans (Eq.cong (λ z → Kab α' w + (- (x * Kab w g) + z))
          (+-identityʳ (- Kab α' g)))
      (Eq.trans (Eq.cong (Kab α' w +_)
          (-‿+-comm (x * Kab w g) (Kab α' g)))
      (Eq.trans (Eq.cong (λ z → Kab α' w + - z)
          (pf-invx x* α' w g awb-g))
        (+-inverseʳ (Kab α' w)))))

    M-return : Φ j₃ mm₂ ≡ mm
    M-return = chain-0 (j₁ ∷ᴸ j₂ ∷ᴸ j₃ ∷ᴸ []ᴸ) mm bv sum0

    ab-eq : _≡_ {A = ℤ ₚ × ℤ ₚ} (₁₊ s , - ₁₊ v) (x * ₁₊ α' , ix * β)
    ab-eq = Eq.cong₂ _,_ (Eq.sym eq-s)
      (Eq.trans (Eq.cong -_ (Eq.sym eq-v)) (-‿involutive (ix * β)))

    c₀ c₁ c₂ c₃ c₄ c₅ cF : C (₂₊ m)
    c₀ = inj₁ (mm  , (bv , ((₁₊ α' , β) , nz)))
    c₁ = inj₁ (mm  , (bv , ((₁₊ α' , ₁₊ w) , λ ())))
    c₂ = inj₁ (mm₁ , (bv , ((₁₊ w , - ₁₊ α') , λ ())))
    c₃ = inj₁ (mm₁ , (bv , ((₁₊ w , ₁₊ v) , λ ())))
    c₄ = inj₁ (mm₂ , (bv , ((₁₊ v , - ₁₊ w) , λ ())))
    c₅ = inj₁ (mm₂ , (bv , ((₁₊ v , ₁₊ s) , λ ())))
    cF = inj₁ (mm  , (bv , ((x * ₁₊ α' , ix * β) , nz')))

    seg₁ : ((ract {₁₊ m} ᵗ) c₀ (S^ x)) .proj₂ ≡ c₁
    seg₁ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm) (proj₂ mm) bv α' β nz (toℕ x))
      (inj₁-a-eq (Eq.cong (₁₊ α' ,_)
        (Eq.trans (Eq.cong (β +_) (nsum-neg x (₁₊ α'))) Xeq)))

    seg₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    seg₂ = inj₁-a-eq Eq.refl

    seg₃ : ((ract {₁₊ m} ᵗ) c₂ (S^ ix)) .proj₂ ≡ c₃
    seg₃ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm₁) (proj₂ mm₁) bv w (- ₁₊ α')
        (λ ()) (toℕ ix))
      (inj₁-a-eq (Eq.cong (₁₊ w ,_)
        (Eq.trans (Eq.cong ((- ₁₊ α') +_) (nsum-neg ix (₁₊ w)))
        (Eq.trans (Eq.cong (λ z → - ₁₊ α' + - (ix * z)) (Eq.sym Xeq))
        (Eq.trans (valM-C x* (₁₊ α') β) eq-v)))))

    seg₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    seg₄ = inj₁-a-eq Eq.refl

    seg₅ : ((ract {₁₊ m} ᵗ) c₄ (S^ x)) .proj₂ ≡ c₅
    seg₅ = Eq.trans
      (ract-S^-inj₁-a+-coset (proj₁ mm₂) (proj₂ mm₂) bv v (- ₁₊ w)
        (λ ()) (toℕ x))
      (inj₁-a-eq (Eq.cong (₁₊ v ,_)
        (Eq.trans (Eq.cong ((- ₁₊ w) +_) (nsum-neg x (₁₊ v)))
        (Eq.trans (Eq.cong₂ (λ z1 z2 → - z1 + - (x * z2))
                    (Eq.sym Xeq) (Eq.sym eq-v))
        (Eq.trans (valM-D x* (₁₊ α') β) eq-s)))))

    seg₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate)) ≡ cF
    seg₆ = Eq.trans (inj₁-a-eq ab-eq)
      (Eq.cong
        (λ zz → inj₁ (zz , (bv , ((x * ₁₊ α' , ix * β) , nz'))))
        M-return)

  ractM-inj₁-nn :
    ((ract {₁₊ m} ᵗ) c₀ (ZM x*)) .proj₂ ≡ cF
  ractM-inj₁-nn =
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

------------------------------------------------------------------------
-- The dispatcher: the full inj₁ M-word action, mirroring ractM!'s
-- internal case tree.

ractM!-inj₁ : ∀ {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m)) (x* : ℤ* ₚ)
  (ab : ℤ ₚ × ℤ ₚ) (nz : ab ≢ (₀ , ₀))
  (nz' : (x* .proj₁ * ab .proj₁ , (x* ⁻¹) .proj₁ * ab .proj₂) ≢ (₀ , ₀)) →
  ((ract {₁₊ m} ᵗ) (inj₁ (mm , (bv , (ab , nz)))) (ZM x*)) .proj₂
  ≡ inj₁ (mm , (bv ,
      ((x* .proj₁ * ab .proj₁ , (x* ⁻¹) .proj₁ * ab .proj₂) , nz')))
ractM!-inj₁ mm bv x* (₀ , ₀) nz nz' = ⊥-elim (nz auto)
ractM!-inj₁ {m} mm bv x* (₀ , ₁₊ β') nz nz' =
  elim-suc (- ((x* ⁻¹) .proj₁ * ₁₊ β'))
           (neg≢0 ((x* ⁻¹) .proj₁ * ₁₊ β')
                  (((x* ⁻¹) *' (₁₊ β' , λ ())) .proj₂))
    λ u eq-u →
  Eq.trans
    (RactM-0b.ractM-inj₁-0b mm bv x* β' nz u eq-u
      (λ e0 → ((x* ⁻¹) *' (₁₊ β' , λ ())) .proj₂ (Eq.cong proj₂ e0)))
    (inj₁-a-eq (Eq.cong (λ z → (z , (x* ⁻¹) .proj₁ * ₁₊ β'))
      (Eq.sym (*-zeroʳ (x* .proj₁)))))
ractM!-inj₁ {m} mm bv x* (₁₊ α' , β) nz nz' =
  elim-fin (β + - (x* .proj₁ * ₁₊ α'))
    (λ Xeq0 →
       elim-suc (- ₁₊ α') (neg≢0 (₁₊ α') λ ()) λ y eq-y →
       elim-suc β
         (λ e0 → (x* *' (₁₊ α' , λ ())) .proj₂
                   (Eq.trans (Eq.sym (+-‿cancel β (x* .proj₁ * ₁₊ α') Xeq0)) e0))
         λ g eq-g →
       RactM-w0.ractM-inj₁-w0 mm bv x* α' β nz y g Xeq0 eq-y eq-g nz')
    (λ w Xeq →
       elim-fin β
         (λ eq-b0 →
            elim-suc (- ₁₊ w) (neg≢0 (₁₊ w) λ ()) λ t eq-t →
            RactM-b0.ractM-inj₁-b0 mm bv x* α' β nz w t Xeq eq-b0 eq-t nz')
         (λ g eq-g →
            elim-suc (- ((x* ⁻¹) .proj₁ * β))
              (neg≢0 ((x* ⁻¹) .proj₁ * β)
                (((x* ⁻¹) *' (β , (λ e0 → suc≢0 (Eq.trans (Eq.sym eq-g) e0))))
                  .proj₂))
              λ v eq-v →
            elim-suc (x* .proj₁ * ₁₊ α') ((x* *' (₁₊ α' , λ ())) .proj₂)
              λ s eq-s →
            RactM-nn.ractM-inj₁-nn mm bv x* α' β nz w v s g
              Xeq eq-v eq-s eq-g nz'))

------------------------------------------------------------------------
-- The M-mul COSET half at inj₁: two M threadings against one, exactly
-- the width-1 argument with ractM!-inj₁ for ractM! (the M column stays
-- at mm throughout).

Mmul-inj₁-coset : ∀ {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (x* y* : ℤ* ₚ) (ab : ℤ ₚ × ℤ ₚ) (nz : ab ≢ (₀ , ₀)) →
  ((ract {₁₊ m} ᵗ) (inj₁ (mm , (bv , (ab , nz)))) (ZM x* • ZM y*)) .proj₂
  ≡ ((ract {₁₊ m} ᵗ) (inj₁ (mm , (bv , (ab , nz)))) (ZM (x* *' y*))) .proj₂
Mmul-inj₁-coset {m} mm bv x* y* ab nz =
  Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (ZM y*)) .proj₂)
             (ractM!-inj₁ mm bv x* ab nz (Mact-nz x* ab nz)))
  (Eq.trans (ractM!-inj₁ mm bv y*
              (x* .proj₁ * ab .proj₁ , (x* ⁻¹) .proj₁ * ab .proj₂)
              (Mact-nz x* ab nz)
              (Mact-nz y* _ (Mact-nz x* ab nz)))
  (Eq.trans (inj₁-a-eq (Eq.cong₂ _,_
      (Eq.trans (Eq.sym (*-assoc (y* .proj₁) (x* .proj₁) (ab .proj₁)))
                (Eq.cong (_* ab .proj₁) (*-comm (y* .proj₁) (x* .proj₁))))
      (Eq.trans (Eq.sym (*-assoc ((y* ⁻¹) .proj₁) ((x* ⁻¹) .proj₁) (ab .proj₂)))
                (Eq.cong (_* ab .proj₂)
                  (Eq.trans (*-comm ((y* ⁻¹) .proj₁) ((x* ⁻¹) .proj₁))
                            (Eq.sym (inv-distrib x* y*)))))))
    (Eq.sym (ractM!-inj₁ mm bv (x* *' y*) ab nz
              (Mact-nz (x* *' y*) ab nz)))))

------------------------------------------------------------------------
-- Block-vs-step: an S-power block whose total weight equals a single
-- exponent is the same M-column update.

blockStep-eq : ∀ {k} (j j' : ℤ ₚ) (t : ℕ) (mm : M (₁₊ k)) (bv : Vec B k) →
  nsum t j ≡ j' →
  itf (λ z → mbSⁿm (toℕ j) z bv) t mm ≡ mbSⁿm (toℕ j') mm bv
blockStep-eq j j' t mm bv weq =
  Eq.trans (mbSⁿ-block j t mm bv)
  (Eq.trans (Eq.cong (λ z → mm ⊞ ζΔ z (MbS-OP.σ bv mm)) weq)
            (Eq.sym (mbSⁿ-shiftζ j' mm bv)))

------------------------------------------------------------------------
-- semi-MS at inj₁, (₀ , ₁₊ β') branch (mirror of SrelWDM.semi-MS-0b):
-- both sides subtract the SAME cascade weight — the image box's
-- exponent is x²·β⁻² (im²x), matching the S^ (x ^2) block's total.

module SemiMS-0b {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (x* : ℤ* ₚ) (β' : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ β') ≢ (₀ , ₀))
  (m₀ : Fin (₁₊ p-2)) (eq-m : (x* ⁻¹) .proj₁ * ₁₊ β' ≡ ₁₊ m₀)
  where

  private
    x  = x* .proj₁
    ix = (x* ⁻¹) .proj₁
    iβ = ((₁₊ β' , λ ()) ⁻¹) .proj₁
    nzM = Mact-nz x* (₀ , ₁₊ β') nz

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    mmB = itf (λ z → mbSⁿm (toℕ (kS0 {m} β' nz)) z bv) (toℕ (x* ^2)) mm

    valAB : _≡_ {A = ℤ ₚ × ℤ ₚ} (x * ₀ , ix * ₁₊ β') (₀ , ₁₊ m₀)
    valAB = Eq.cong₂ _,_ (*-zeroʳ x) eq-m

    im-eq : ((₁₊ m₀ , λ ()) ⁻¹) .proj₁ ≡ x * iβ
    im-eq = Eq.trans
      (inv-cong (₁₊ m₀ , λ ()) ((x* ⁻¹) *' (₁₊ β' , λ ())) (Eq.sym eq-m))
      (Eq.trans (inv-distrib (x* ⁻¹) (₁₊ β' , λ ()))
                (Eq.cong (_* iβ) (inv-involutive x*)))

    im²x : sqInv m₀ ≡ (x* ^2) * sqInv β'
    im²x = Eq.trans (Eq.cong₂ _*_ im-eq im-eq)
      (Eq.trans (*-assoc x iβ (x * iβ))
      (Eq.trans (Eq.cong (x *_) (Eq.sym (*-assoc iβ x iβ)))
      (Eq.trans (Eq.cong (λ z → x * (z * iβ)) (*-comm iβ x))
      (Eq.trans (Eq.cong (x *_) (*-assoc x iβ iβ))
                (Eq.sym (*-assoc x x (iβ * iβ)))))))

    wEq : nsum (toℕ (x* ^2)) (kS0 {m} β' nz) ≡ kS0 {m} m₀ (λ ())
    wEq = Eq.trans (Eq.cong (nsum (toℕ (x* ^2))) (kS0-val {m} β' nz))
      (Eq.trans (nsum-* (x* ^2) (sqInv β'))
        (Eq.sym (Eq.trans (kS0-val {m} m₀ (λ ())) im²x)))

  semiMS-inj₁-0b :
    ((ract {₁₊ m} ᵗ)
       (inj₁ (mm , (bv , ((₀ , ₁₊ β') , nz)))) (ZM x* • S)) .proj₂
    ≡ ((ract {₁₊ m} ᵗ)
       (inj₁ (mm , (bv , ((₀ , ₁₊ β') , nz)))) (S^ (x* ^2) • ZM x*)) .proj₂
  semiMS-inj₁-0b =
    Eq.trans (Eq.cong (λ c → proj₂ (ract {₁₊ m} c (gate₁ S-gate)))
        (Eq.trans (ractM!-inj₁ mm bv x* (₀ , ₁₊ β') nz nzM)
                  (inj₁-a-eq {ny = λ ()} valAB)))
    (Eq.sym
      (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (ZM x*)) .proj₂)
          (ract-S^-inj₁-0b-coset mm bv β' nz (toℕ (x* ^2))))
      (Eq.trans (Eq.trans (ractM!-inj₁ mmB bv x* (₀ , ₁₊ β') nz nzM)
                          (inj₁-a-eq {ny = λ ()} valAB))
        (Eq.cong (λ zz → inj₁ (zz , (bv , ((₀ , ₁₊ m₀) , λ ()))))
          (blockStep-eq (kS0 {m} β' nz) (kS0 {m} m₀ (λ ()))
            (toℕ (x* ^2)) mm bv wEq)))))

------------------------------------------------------------------------
-- semi-MS at inj₁, (₁₊ α' , β) branch (mirror of SrelWDM.semi-MS-nn):
-- no cascade weight on either side — the S letters are absorbed by the
-- a ≠ 0 boxes, and the values agree by x⁻¹·(β − x²α) ≡ x⁻¹β − xα.

module SemiMS-nn {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (x* : ℤ* ₚ) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀))
  (s : Fin (₁₊ p-2)) (eq-s : x* .proj₁ * ₁₊ α' ≡ ₁₊ s)
  where

  private
    x  = x* .proj₁
    ix = (x* ⁻¹) .proj₁
    instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}
    nzM = Mact-nz x* (₁₊ α' , β) nz

    B2 = β + - ((x* ^2) * ₁₊ α')

    ix-x² : ix * (x* ^2) ≡ x
    ix-x² = Eq.trans (Eq.sym (*-assoc ix x x))
      (Eq.trans (Eq.cong (_* x) (lemma-⁻¹ˡ x {{instᵢ}}))
                (*-identityˡ x))

    ixB2 : ix * B2 ≡ (ix * β) + - (x * ₁₊ α')
    ixB2 = Eq.trans (*-distribˡ-+ ix β (- ((x* ^2) * ₁₊ α')))
      (Eq.cong ((ix * β) +_)
        (Eq.trans (Eq.sym (-‿distribʳ-* ix ((x* ^2) * ₁₊ α')))
          (Eq.cong -_
            (Eq.trans (Eq.sym (*-assoc ix (x* ^2) (₁₊ α')))
                      (Eq.cong (_* ₁₊ α') ix-x²)))))

    valAB : _≡_ {A = ℤ ₚ × ℤ ₚ} (x * ₁₊ α' , ix * β) (₁₊ s , ix * β)
    valAB = Eq.cong (_, ix * β) eq-s

    boxF : _≡_ {A = ℤ ₚ × ℤ ₚ} (x * ₁₊ α' , ix * B2)
           (₁₊ s , (ix * β) + - ₁₊ s)
    boxF = Eq.cong₂ _,_ eq-s
      (Eq.trans ixB2
        (Eq.cong ((ix * β) +_) (Eq.cong -_ eq-s)))

  semiMS-inj₁-nn :
    ((ract {₁₊ m} ᵗ)
       (inj₁ (mm , (bv , ((₁₊ α' , β) , nz)))) (ZM x* • S)) .proj₂
    ≡ ((ract {₁₊ m} ᵗ)
       (inj₁ (mm , (bv , ((₁₊ α' , β) , nz)))) (S^ (x* ^2) • ZM x*)) .proj₂
  semiMS-inj₁-nn =
    Eq.trans (Eq.cong (λ c → proj₂ (ract {₁₊ m} c (gate₁ S-gate)))
        (Eq.trans (ractM!-inj₁ mm bv x* (₁₊ α' , β) nz nzM)
                  (inj₁-a-eq valAB)))
    (Eq.trans (Eq.cong proj₂
        (ract-S-inj₁-a+ (proj₁ mm) (proj₂ mm) bv s (ix * β) (λ ())))
    (Eq.sym
      (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (ZM x*)) .proj₂)
          (Eq.trans
            (ract-S^-inj₁-a+-coset (proj₁ mm) (proj₂ mm) bv α' β nz
              (toℕ (x* ^2)))
            (inj₁-a-eq (Eq.cong (₁₊ α' ,_)
              (Eq.cong (β +_) (nsum-neg (x* ^2) (₁₊ α')))))))
      (Eq.trans (ractM!-inj₁ mm bv x* (₁₊ α' , B2) (λ ())
                  (Mact-nz x* (₁₊ α' , B2) (λ ())))
                (inj₁-a-eq boxF)))))

------------------------------------------------------------------------
-- Sealed per-family dispatchers: the COSET (≡) component of srel-wd at
-- inj₁ for every unary axiom family, with the box dispatch (elim-suc /
-- elim-fin, mirroring the width-1 clauses) done INSIDE.  Each is
-- stated exactly as the hole's obligation, so a future fill consumes
-- it with no further case analysis.

orderS-inj₁-coset : ∀ {m : ℕ} (ml' : ML' (₂₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₁ ml') (S ^ p)) .proj₂
  ≡ ((ract {₁₊ m} ᵗ) (inj₁ ml') ε) .proj₂
orderS-inj₁-coset ((dv , e) , (bv , ((₀ , ₀) , nz))) = ⊥-elim (nz auto)
orderS-inj₁-coset ((dv , e) , (bv , ((₀ , ₁₊ b') , nz))) =
  orderS-inj₁-0b-coset (dv , e) bv b' nz
orderS-inj₁-coset ((dv , e) , (bv , ((₁₊ a₀ , b) , nz))) =
  proj₂ (orderS-inj₁-a+ dv e bv a₀ b nz)

-- NOTE: sealed dispatchers for the kHn-heavy families (order-H,
-- order-SH, comm-HHS) blow up the checker (the nested elim-suc motives
-- re-instantiate conversion-heavy types); their per-branch lemmas in
-- PushWD take the same hypothesis shapes as the width-1 clauses, so
-- the dispatch belongs at the eventual srel-wd fill site instead.

semiMS-inj₁-coset : ∀ {m : ℕ} (x* : ℤ* ₚ) (ml' : ML' (₂₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₁ ml') (ZM x* • S)) .proj₂
  ≡ ((ract {₁₊ m} ᵗ) (inj₁ ml') (S^ (x* ^2) • ZM x*)) .proj₂
semiMS-inj₁-coset x* ((dv , e) , (bv , ((₀ , ₀) , nz))) =
  ⊥-elim (nz auto)
semiMS-inj₁-coset x* ((dv , e) , (bv , ((₀ , ₁₊ β') , nz))) =
  elim-suc ((x* ⁻¹) .proj₁ * ₁₊ β')
           (((x* ⁻¹) *' (₁₊ β' , λ ())) .proj₂)
    λ m₀ eq-m →
  SemiMS-0b.semiMS-inj₁-0b (dv , e) bv x* β' nz m₀ eq-m
semiMS-inj₁-coset x* ((dv , e) , (bv , ((₁₊ α' , β) , nz))) =
  elim-suc (x* .proj₁ * ₁₊ α') ((x* *' (₁₊ α' , λ ())) .proj₂)
    λ s eq-s →
  SemiMS-nn.semiMS-inj₁-nn (dv , e) bv x* α' β nz s eq-s

Mmul-inj₁-coset-full : ∀ {m : ℕ} (x* y* : ℤ* ₚ) (ml' : ML' (₂₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₁ ml') (ZM x* • ZM y*)) .proj₂
  ≡ ((ract {₁₊ m} ᵗ) (inj₁ ml') (ZM (x* *' y*))) .proj₂
Mmul-inj₁-coset-full x* y* ((dv , e) , (bv , (ab , nz))) =
  Mmul-inj₁-coset (dv , e) bv x* y* ab nz

------------------------------------------------------------------------
-- comm-CZ-S↑ at width 2 (the inj₂ (d , ml1) hole), COSET half.  The
-- CZ collapse (LCZ2 via TDw.push-D-w) reads only the A box's shape,
-- and the S↑ recursion updates the A box exactly as B-Top's b'-of
-- does after the collapse — on every branch the two normal forms share
-- all their (stuck) engine terms and differ only in the E slot, closed
-- by +-swap / e+-0.  Slot congruences absorb the where-lifted
-- nonzeroness proofs as implicits.

inj₂-w1-e-eq : ∀ {d : D} {e e' : E} {a : A} → e ≡ e' →
  _≡_ {A = C 2}
    (inj₂ (d , (([] , e) , ([] , a))))
    (inj₂ (d , (([] , e') , ([] , a))))
inj₂-w1-e-eq Eq.refl = Eq.refl

inj₁-e-eq : ∀ {m : ℕ} {dv : Vec D (₁₊ m)} {e e' : E} {bv : Vec B (₁₊ m)}
  {x : ℤ ₚ × ℤ ₚ} {nx : x ≢ (₀ , ₀)} → e ≡ e' →
  _≡_ {A = C (₂₊ m)}
    (inj₁ ((dv , e) , (bv , (x , nx))))
    (inj₁ ((dv , e') , (bv , (x , nx))))
inj₁-e-eq Eq.refl = Eq.refl

commCZS↑-w2-coset : ∀ (d : D) (e : E) (ab : ℤ ₚ × ℤ ₚ)
  (nz : ab ≢ (₀ , ₀)) →
  ((ract {1} ᵗ)
     (inj₂ (d , (([] , e) , ([] , (ab , nz))))) (CZ • S ↑)) .proj₂
  ≡ ((ract {1} ᵗ)
     (inj₂ (d , (([] , e) , ([] , (ab , nz))))) (S ↑ • CZ)) .proj₂
commCZS↑-w2-coset d e (₀ , ₀) nz = ⊥-elim (nz auto)
commCZS↑-w2-coset d e (₀ , ₁₊ b) nz =
  inj₂-w1-e-eq (+-swap e
    (- (TDw.push-D-w d
         (LCZ2.dir-of (inj₂ ([] , ((₀ , ₁₊ b) , nz))))
         (TDw.dir-of₂-No-Top-H (inj₂ ([] , ((₀ , ₁₊ b) , nz)))) .proj₁))
    (- (A-dir-S-power {0} ((₀ , ₁₊ b) , nz) (gate₁ S-gate) _ .proj₁)))
commCZS↑-w2-coset d e (₁₊ α , ₀) nz =
  inj₁-e-eq (Eq.cong
    (_+ - (TDw.push-D-w d
            (LCZ2.dir-of (inj₂ ([] , ((₁₊ α , ₀) , nz))))
            (TDw.dir-of₂-No-Top-H (inj₂ ([] , ((₁₊ α , ₀) , nz))))
            .proj₁))
    (Eq.sym (e+-0 e)))
commCZS↑-w2-coset d e (₁₊ α , ₁₊ β') nz =
  inj₁-e-eq (Eq.cong
    (_+ - (TDw.push-D-w d
            (LCZ2.dir-of (inj₂ ([] , ((₁₊ α , ₁₊ β') , nz))))
            (TDw.dir-of₂-No-Top-H (inj₂ ([] , ((₁₊ α , ₁₊ β') , nz))))
            .proj₁))
    (Eq.sym (e+-0 e)))

------------------------------------------------------------------------
-- comm-CZ-S↓ at width 2, A = (₀ , ₁₊ b) branch, COSET half.  Here the
-- S hits the bottom D box (d-of-DS) while the CZ collapse pushes the
-- all-CZ word CZ^ b⁻¹ through the same box: the two box updates are
-- b-translations that commute (G1), and the emitted exponent depends
-- only on the box's a-component, which both preserve (E1).

-- The CZ-power push's emitted exponent: nsum t (eCZ a), b-independent.
E1 : ∀ (t : ℕ) (a b : ℤ ₚ) →
  TDw.push-D-w (a , b) (CZ ^ t) (TDw.ntH-^ TDw.ntH-CZ t) .proj₁
  ≡ nsum t (eCZ a)
E1 zero a b = Eq.refl
E1 (suc zero) ₀      ₀      = Eq.sym (+-identityʳ ₀)
E1 (suc zero) ₀      (₁₊ _) = Eq.sym (+-identityʳ ₀)
E1 (suc zero) (₁₊ i) ₀      = Eq.sym (+-identityʳ (₁₊ i))
E1 (suc zero) (₁₊ i) (₁₊ _) = Eq.sym (+-identityʳ (₁₊ i))
E1 (suc (suc t)) ₀ ₀ =
  Eq.cong (₀ +_) (E1 (suc t) ₀ (₀ + - ₁))
E1 (suc (suc t)) ₀ (₁₊ b') =
  Eq.cong (₀ +_) (E1 (suc t) ₀ (₁₊ b' + - ₁))
E1 (suc (suc t)) (₁₊ i) ₀ =
  Eq.cong (₁₊ i +_) (E1 (suc t) (₁₊ i) (₀ + - ₁))
E1 (suc (suc t)) (₁₊ i) (₁₊ b') =
  Eq.cong (₁₊ i +_) (E1 (suc t) (₁₊ i) (₁₊ b' + - ₁))

-- d-of-DS commutes with the CZ-power push on the D box.
G1 : ∀ (t : ℕ) (a b : ℤ ₚ) →
  d-of-DS (TDw.push-D-w (a , b) (CZ ^ t) (TDw.ntH-^ TDw.ntH-CZ t)
             .proj₂ .proj₂)
  ≡ TDw.push-D-w (d-of-DS (a , b)) (CZ ^ t) (TDw.ntH-^ TDw.ntH-CZ t)
      .proj₂ .proj₂
G1 zero ₀      b = Eq.refl
G1 zero (₁₊ i) b = Eq.refl
G1 (suc zero) ₀      b = Eq.refl
G1 (suc zero) (₁₊ i) b =
  Eq.cong (λ z → (₁₊ i , z)) (+-swap b (- ₁) (- ₁₊ i))
G1 (suc (suc t)) ₀ b = G1 (suc t) ₀ (b + - ₁)
G1 (suc (suc t)) (₁₊ i) b =
  Eq.trans (G1 (suc t) (₁₊ i) (b + - ₁))
    (Eq.cong
      (λ z → TDw.push-D-w (₁₊ i , z) (CZ ^ suc t)
               (TDw.ntH-^ TDw.ntH-CZ (suc t)) .proj₂ .proj₂)
      (+-swap b (- ₁) (- ₁₊ i)))

-- Slot congruence: rewrite the D and E slots of a width-2 inj₂ coset.
inj₂-w1-de-eq : ∀ {d d' : D} {e e' : E} {a : A} → d ≡ d' → e ≡ e' →
  _≡_ {A = C 2}
    (inj₂ (d , (([] , e) , ([] , a))))
    (inj₂ (d' , (([] , e') , ([] , a))))
inj₂-w1-de-eq Eq.refl Eq.refl = Eq.refl

commCZS↓-w2-0b-coset : ∀ (d : D) (e : E) (b : Fin (₁₊ p-2))
  (nz : (₀ , ₁₊ b) ≢ (₀ , ₀)) →
  ((ract {1} ᵗ)
     (inj₂ (d , (([] , e) , ([] , ((₀ , ₁₊ b) , nz))))) (CZ • S ↓)) .proj₂
  ≡ ((ract {1} ᵗ)
     (inj₂ (d , (([] , e) , ([] , ((₀ , ₁₊ b) , nz))))) (S ↓ • CZ)) .proj₂
commCZS↓-w2-0b-coset (₀ , db) e b nz =
  inj₂-w1-de-eq (G1 (toℕ (((₁₊ b , λ ()) ⁻¹) .proj₁)) ₀ db) Eq.refl
commCZS↓-w2-0b-coset (₁₊ a' , db) e b nz =
  inj₂-w1-de-eq
    (G1 (toℕ (((₁₊ b , λ ()) ⁻¹) .proj₁)) (₁₊ a') db)
    (Eq.cong (λ z → e + - z)
      (Eq.trans (E1 (toℕ (((₁₊ b , λ ()) ⁻¹) .proj₁)) (₁₊ a') db)
        (Eq.sym (E1 (toℕ (((₁₊ b , λ ()) ⁻¹) .proj₁)) (₁₊ a')
          (db + - ₁₊ a')))))

------------------------------------------------------------------------
-- Width-2 push-D-w closed forms for the cascade-vs-collapse identity
-- (the (₁₊ α , β) branch of comm-CZ-S↓ at width 2).  Phase 1: the
-- S-power and H closed forms and eCZ's identity nature.

-- eCZ is the identity (it is defined by cases only to make the
-- width-2 base facts reduce).
eCZ-id : ∀ (x : ℤ ₚ) → eCZ x ≡ x
eCZ-id ₀      = Eq.refl
eCZ-id (₁₊ i) = Eq.refl

-- S-power through a D box: no emission, b shifts by nsum t (− a).
ES : ∀ (t : ℕ) (a b : ℤ ₚ) →
  TDw.push-D-w (a , b) (S ^ t) (TDw.ntH-^ TDw.ntH-S t) .proj₁ ≡ ₀
ES zero a b = Eq.refl
ES (suc zero) ₀      ₀      = Eq.refl
ES (suc zero) ₀      (₁₊ _) = Eq.refl
ES (suc zero) (₁₊ i) ₀      = Eq.refl
ES (suc zero) (₁₊ i) (₁₊ _) = Eq.refl
ES (suc (suc t)) ₀ ₀ =
  Eq.trans (Eq.cong (₀ +_) (ES (suc t) ₀ (₀ + - ₀))) (+-identityʳ ₀)
ES (suc (suc t)) ₀ (₁₊ b') =
  Eq.trans (Eq.cong (₀ +_) (ES (suc t) ₀ (₁₊ b' + - ₀))) (+-identityʳ ₀)
ES (suc (suc t)) (₁₊ i) ₀ =
  Eq.trans (Eq.cong (₀ +_) (ES (suc t) (₁₊ i) (₀ + - ₁₊ i)))
    (+-identityʳ ₀)
ES (suc (suc t)) (₁₊ i) (₁₊ b') =
  Eq.trans (Eq.cong (₀ +_) (ES (suc t) (₁₊ i) (₁₊ b' + - ₁₊ i)))
    (+-identityʳ ₀)

GS : ∀ (t : ℕ) (a b : ℤ ₚ) →
  TDw.push-D-w (a , b) (S ^ t) (TDw.ntH-^ TDw.ntH-S t) .proj₂ .proj₂
  ≡ (a , b + nsum t (- a))
GS zero a b = Eq.cong (a ,_) (Eq.sym (+-identityʳ b))
GS (suc zero) a b =
  Eq.cong (a ,_) (Eq.cong (b +_) (Eq.sym (+-identityʳ (- a))))
GS (suc (suc t)) a b =
  Eq.trans (GS (suc t) a (b + - a))
    (Eq.cong (a ,_) (+-assoc b (- a) (nsum (suc t) (- a))))

-- One H through a D box: the quarter turn, no emission (projection
-- forms; d'-of needs no component split).
GH : ∀ (a b : ℤ ₚ) →
  TDw.push-D-w (a , b) H TDw.ntH-H .proj₂ .proj₂ ≡ (b , - a)
GH a b = Eq.refl

EH : ∀ (a b : ℤ ₚ) →
  TDw.push-D-w (a , b) H TDw.ntH-H .proj₁ ≡ ₀
EH ₀      ₀      = Eq.refl
EH ₀      (₁₊ _) = Eq.refl
EH (₁₊ i) ₀      = Eq.refl
EH (₁₊ i) (₁₊ _) = Eq.refl
