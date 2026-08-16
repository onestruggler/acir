------------------------------------------------------------------------
-- Presentations of groups
--
-- Well-definedness of the coset action on the group-specific axioms
-- (the srel case of ⁻¹[⇑]-wd'' in Normalization.agda), one axiom at a
-- time.  For an axiom u === t we must show the threaded action agrees:
-- (ract ᵗ) c u ≋ (ract ᵗ) c t.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (dir-of-DS ; d-of-DS)
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Data.Nat using (zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (_%_ ; m%n<n)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ<)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥-elim)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime

------------------------------------------------------------------------
-- Value-level machinery for the M-word cases (M-mul, semi-MS).
--
-- The S-power and H updates of the A box agree, on values, with the
-- total affine maps valS / valH (up to -0/+0 normalisation at the zero
-- patterns).  The M word S^x•H•S^x⁻¹•H•S^x•H then acts on values as
-- diag(x, x⁻¹) — proven once, by ring algebra, in valM-orbit.

-- Iterated S-steps sum to a ring multiplication.
nsum-* : ∀ (x v : ℤ ₚ) → nsum (toℕ x) v ≡ x * v
nsum-* x v = toℕ-injective
  (Eq.trans (nsum-toℕ (toℕ x) v)
            (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ x *ℕ toℕ v) p))))

nsum-neg : ∀ (x a : ℤ ₚ) → nsum (toℕ x) (- a) ≡ - (x * a)
nsum-neg x a = Eq.trans (nsum-* x (- a)) (Eq.sym (-‿distribʳ-* x a))

valS : ℤ ₚ → ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
valS k (a , b) = a , b + - (k * a)

valH : ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
valH (a , b) = b , - a

valS-0 : ∀ (k β : ℤ ₚ) → valS k (₀ , β) ≡ (₀ , β)
valS-0 k β = Eq.cong (₀ ,_)
  (Eq.trans (Eq.cong (λ v → β + - v) (*-zeroʳ k)) (e+-0 β))

-- The two nontrivial value computations of the M-word orbit, standalone
-- (they are also needed mid-threading in the ractM lemmas below).
valM-C : ∀ (x* : ℤ* ₚ) (α β : ℤ ₚ) →
  let x = x* .proj₁ ; ix = (x* ⁻¹) .proj₁ in
  - α + - (ix * (β + - (x * α))) ≡ - (ix * β)
valM-C x* α β =
  Eq.trans (Eq.cong (λ v → - α + - v) ixB1)
  (Eq.trans (Eq.cong (- α +_) (Eq.sym (-‿+-comm (ix * β) (- α))))
  (Eq.trans (Eq.cong (λ v → - α + (- (ix * β) + v)) (-‿involutive α))
  (Eq.trans (Eq.cong (- α +_) (+-comm (- (ix * β)) α))
  (Eq.trans (Eq.sym (+-assoc (- α) α (- (ix * β))))
  (Eq.trans (Eq.cong (_+ - (ix * β)) (+-inverseˡ α))
            (+-0ˡ (- (ix * β))))))))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁
  instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}

  ixB1 : ix * (β + - (x * α)) ≡ ix * β + - α
  ixB1 = Eq.trans (*-distribˡ-+ ix β (- (x * α)))
         (Eq.cong (ix * β +_)
           (Eq.trans (Eq.sym (-‿distribʳ-* ix (x * α)))
           (Eq.cong -_
             (Eq.trans (Eq.sym (*-assoc ix x α))
             (Eq.trans (Eq.cong (_* α) (lemma-⁻¹ˡ x {{instᵢ}}))
                       (*-identityˡ α))))))

valM-D : ∀ (x* : ℤ* ₚ) (α β : ℤ ₚ) →
  let x = x* .proj₁ ; ix = (x* ⁻¹) .proj₁ in
  - (β + - (x * α)) + - (x * - (ix * β)) ≡ x * α
valM-D x* α β =
  Eq.trans (Eq.cong (λ v → - (β + - (x * α)) + - v) xC)
  (Eq.trans (Eq.cong (- (β + - (x * α)) +_) (-‿involutive β))
  (Eq.trans (Eq.cong (_+ β)
    (Eq.trans (Eq.sym (-‿+-comm β (- (x * α))))
    (Eq.trans (Eq.cong (- β +_) (-‿involutive (x * α)))
              (+-comm (- β) (x * α)))))
  (Eq.trans (+-assoc (x * α) (- β) β)
  (Eq.trans (Eq.cong (x * α +_) (+-inverseˡ β))
            (+-identityʳ (x * α))))))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁
  instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}

  xC : x * - (ix * β) ≡ - β
  xC = Eq.trans (Eq.sym (-‿distribʳ-* x (ix * β)))
       (Eq.cong -_
         (Eq.trans (Eq.sym (*-assoc x ix β))
         (Eq.trans (Eq.cong (_* β) (lemma-⁻¹ʳ x {{instᵢ}}))
                   (*-identityˡ β))))

-- The M word acts on values as diag(x, x⁻¹).
valM-orbit : ∀ (x* : ℤ* ₚ) (α β : ℤ ₚ) →
  let x = x* .proj₁ ; ix = (x* ⁻¹) .proj₁ in
  valH (valS x (valH (valS ix (valH (valS x (α , β)))))) ≡ (x * α , ix * β)
valM-orbit x* α β = Eq.cong₂ _,_
  (Eq.trans (Eq.cong (λ v → - (β + - (x * α)) + - (x * v)) (valM-C x* α β))
            (valM-D x* α β))
  (Eq.trans (Eq.cong -_ (valM-C x* α β)) (-‿involutive (ix * β)))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁

-- Threading the M word through a width-1 coset, (₀ , β) branch: the
-- value follows diag(x, x⁻¹) ((₀,β) ↦ (₀, x⁻¹β)) and the two escape
-- powers cancel: x·β⁻² from the leading S^x on the a = 0 box against
-- the H power (β·(-x⁻¹β))⁻¹ ≡ -(x·β⁻²).
ractM-0b : ∀ (x* : ℤ* ₚ) (e : E) (β' : Fin (₁₊ p-2))
  (nz : (₀ , ₁₊ β') ≢ (₀ , ₀)) (u : Fin (₁₊ p-2)) →
  - ((x* ⁻¹) .proj₁ * ₁₊ β') ≡ ₁₊ u →
  (nz' : (₀ , (x* ⁻¹) .proj₁ * ₁₊ β') ≢ (₀ , ₀)) →
  ((ract {0} ᵗ) (mk e (₀ , ₁₊ β') nz) (ZM x*)) .proj₂
  ≡ mk e (₀ , (x* ⁻¹) .proj₁ * ₁₊ β') nz'
ractM-0b x* e β' nz u eq-u nz' =
  Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W5 .proj₂) c₁eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W3 .proj₂) c₃eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W1 .proj₂) c₅eq)
            (c1-eq e-fix ab-eq)))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁
  β  = ₁₊ β'
  β* : ℤ* ₚ
  β* = (₁₊ β' , λ ())
  instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}

  W1 W3 W5 : Circuit 1
  W1 = H
  W3 = H • (S^ x • H)
  W5 = H • (S^ ix • W3)

  K0 = kS-a0 β' nz

  c₁eq : ((ract {0} ᵗ) (mk e (₀ , ₁₊ β') nz) (S^ x)) .proj₂
         ≡ mk (e + - (x * K0)) (₀ , ₁₊ β') nz
  c₁eq = Eq.trans (ract1-S^-a0 (toℕ x) e β' nz)
                  (c1-eq (Eq.cong (e +_) (nsum-neg x K0)) Eq.refl)

  e₂ = (e + - (x * K0)) + - ₀

  c₃eq : ((ract {0} ᵗ) (mk e₂ (₁₊ β' , ₀) (λ ())) (S^ ix)) .proj₂
         ≡ mk e₂ (₁₊ β' , ₁₊ u) (λ ())
  c₃eq = Eq.trans (ract1-S^-a+ (toℕ ix) e₂ β' ₀ (λ ()))
           (c1-eq Eq.refl (Eq.cong (₁₊ β' ,_)
             (Eq.trans (+-0ˡ _) (Eq.trans (nsum-neg ix β) eq-u))))

  e₄ = e₂ + - Kab β' u

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

  c₅eq : ((ract {0} ᵗ) (mk e₄ (₁₊ u , - β) (λ ())) (S^ x)) .proj₂
         ≡ mk e₄ (₁₊ u , ₀) (λ ())
  c₅eq = Eq.trans (ract1-S^-a+ (toℕ x) e₄ u (- β) (λ ()))
                  (c1-eq Eq.refl (Eq.cong (₁₊ u ,_) val5))

  Q : ((((x* ⁻¹)) *' (β* *' β*)) ⁻¹) .proj₁ ≡ x * K0
  Q = Eq.trans (inv-distrib (x* ⁻¹) (β* *' β*))
               (Eq.cong₂ _*_ (inv-involutive x*) (inv-distrib β* β*))

  Kfix : Kab β' u ≡ - (x * K0)
  Kfix = Eq.trans
    (inv-cong (β* *' (₁₊ u , λ ())) (-' ((x* ⁻¹) *' (β* *' β*)))
      (Eq.trans (Eq.cong (β *_) (Eq.sym eq-u))
      (Eq.trans (Eq.sym (-‿distribʳ-* β (ix * β)))
      (Eq.cong -_
        (Eq.trans (Eq.sym (*-assoc β ix β))
        (Eq.trans (Eq.cong (_* β) (*-comm β ix))
                  (*-assoc ix β β)))))))
    (Eq.trans (inv-neg-comm ((x* ⁻¹) *' (β* *' β*))) (Eq.cong -_ Q))

  ab-eq : (₀ , - ₁₊ u) ≡ (₀ , ix * β)
  ab-eq = Eq.cong (₀ ,_)
    (Eq.trans (Eq.cong -_ (Eq.sym eq-u)) (-‿involutive (ix * β)))

  e-fix : (e₄ + - ₀) ≡ e
  e-fix = Eq.trans (e+-0 e₄)
          (Eq.trans (Eq.cong (_+ - Kab β' u) (e+-0 (e + - (x * K0))))
          (Eq.trans (Eq.cong ((e + - (x * K0)) +_) (Eq.cong -_ Kfix))
                    (cancel-+ e (x * K0))))

-- Threading the M word, generic branch (α ≠ 0, β ≠ 0, β − xα ≠ 0):
-- value follows diag(x, x⁻¹); the three H escape powers telescope by
-- the x-scaled partial fraction.
ractM-nn : ∀ (x* : ℤ* ₚ) (e : E) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀)) (w v s g : Fin (₁₊ p-2)) →
  β + - (x* .proj₁ * ₁₊ α') ≡ ₁₊ w →
  - ((x* ⁻¹) .proj₁ * β) ≡ ₁₊ v →
  x* .proj₁ * ₁₊ α' ≡ ₁₊ s →
  β ≡ ₁₊ g →
  (nz' : (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) ≢ (₀ , ₀)) →
  ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (ZM x*)) .proj₂
  ≡ mk e (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) nz'
ractM-nn x* e α' β nz w v s g Xeq eq-v eq-s eq-g nz' =
  Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W5 .proj₂) c₁eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W3 .proj₂) c₃eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W1 .proj₂) c₅eq)
            (c1-eq e-fix ab-eq)))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁

  W1 W3 W5 : Circuit 1
  W1 = H
  W3 = H • (S^ x • H)
  W5 = H • (S^ ix • W3)

  c₁eq : ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (S^ x)) .proj₂
         ≡ mk e (₁₊ α' , ₁₊ w) (λ ())
  c₁eq = Eq.trans (ract1-S^-a+ (toℕ x) e α' β nz)
           (c1-eq Eq.refl (Eq.cong (₁₊ α' ,_)
             (Eq.trans (Eq.cong (β +_) (nsum-neg x (₁₊ α'))) Xeq)))

  e₂ = e + - Kab α' w

  c₃eq : ((ract {0} ᵗ) (mk e₂ (₁₊ w , - ₁₊ α') (λ ())) (S^ ix)) .proj₂
         ≡ mk e₂ (₁₊ w , ₁₊ v) (λ ())
  c₃eq = Eq.trans (ract1-S^-a+ (toℕ ix) e₂ w (- ₁₊ α') (λ ()))
           (c1-eq Eq.refl (Eq.cong (₁₊ w ,_)
             (Eq.trans (Eq.cong ((- ₁₊ α') +_) (nsum-neg ix (₁₊ w)))
             (Eq.trans (Eq.cong (λ z → - ₁₊ α' + - (ix * z)) (Eq.sym Xeq))
             (Eq.trans (valM-C x* (₁₊ α') β) eq-v)))))

  e₄ = e₂ + - Kab w v

  c₅eq : ((ract {0} ᵗ) (mk e₄ (₁₊ v , - ₁₊ w) (λ ())) (S^ x)) .proj₂
         ≡ mk e₄ (₁₊ v , ₁₊ s) (λ ())
  c₅eq = Eq.trans (ract1-S^-a+ (toℕ x) e₄ v (- ₁₊ w) (λ ()))
           (c1-eq Eq.refl (Eq.cong (₁₊ v ,_)
             (Eq.trans (Eq.cong ((- ₁₊ w) +_) (nsum-neg x (₁₊ v)))
             (Eq.trans (Eq.cong₂ (λ z1 z2 → - z1 + - (x * z2))
                         (Eq.sym Xeq) (Eq.sym eq-v))
             (Eq.trans (valM-D x* (₁₊ α') β) eq-s)))))

  ab-eq : (₁₊ s , - ₁₊ v) ≡ (x * ₁₊ α' , ix * β)
  ab-eq = Eq.cong₂ _,_ (Eq.sym eq-s)
            (Eq.trans (Eq.cong -_ (Eq.sym eq-v)) (-‿involutive (ix * β)))

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
    (Eq.trans (inv-neg-comm ((x* ⁻¹) *' ((₁₊ w , λ ()) *' (₁₊ g , λ ()))))
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
        (Eq.trans (Eq.cong (_* (β * ₁₊ α'))
                    (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = x* .proj₂}}}))
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

  e-fix : (e₄ + - Kab v s) ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_ (Eq.cong ((e + - Kab α' w) +_) (Eq.cong -_ I1))
                  (Eq.cong -_ I2))
    (Eq.trans
      (Eq.cong₂ _+_
        (Eq.cong ((e + - Kab α' w) +_) (-‿involutive (x * Kab w g)))
        (-‿involutive (Kab α' g)))
    (Eq.trans (Eq.cong (_+ Kab α' g) (+-assoc e (- Kab α' w) (x * Kab w g)))
    (Eq.trans (+-assoc e (- Kab α' w + x * Kab w g) (Kab α' g))
    (Eq.trans (Eq.cong (e +_)
      (Eq.trans (+-assoc (- Kab α' w) (x * Kab w g) (Kab α' g))
      (Eq.trans (Eq.cong (- Kab α' w +_) (pf-invx x* α' w g awb-g))
                (+-inverseˡ (Kab α' w)))))
      (+-identityʳ e)))))

-- Threading the M word, β = xα branch (the first H hits an (a,0) box).
ractM-w0 : ∀ (x* : ℤ* ₚ) (e : E) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀)) (y g : Fin (₁₊ p-2)) →
  β + - (x* .proj₁ * ₁₊ α') ≡ ₀ →
  - ₁₊ α' ≡ ₁₊ y →
  β ≡ ₁₊ g →
  (nz' : (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) ≢ (₀ , ₀)) →
  ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (ZM x*)) .proj₂
  ≡ mk e (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) nz'
ractM-w0 x* e α' β nz y g Xeq0 eq-y eq-g nz' =
  Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W5 .proj₂) c₁eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W4 .proj₂)
              (c1-eq {e = e + - ₀} {nz' = λ ()} Eq.refl (Eq.cong (₀ ,_) eq-y)))
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W3 .proj₂) c₃eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W1 .proj₂) c₅eq)
            (c1-eq e-fix ab-eq))))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁
  instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}
  iα = ((₁₊ α' , λ ()) ⁻¹) .proj₁
  Ky = kS-a0 y (λ ())
  V  = ix * (iα * iα)

  W1 W3 W4 W5 : Circuit 1
  W1 = H
  W3 = H • (S^ x • H)
  W4 = S^ ix • W3
  W5 = H • W4

  beq : β ≡ x * ₁₊ α'
  beq = +-‿cancel β (x * ₁₊ α') Xeq0

  c₁eq : ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (S^ x)) .proj₂
         ≡ mk e (₁₊ α' , ₀) (λ ())
  c₁eq = Eq.trans (ract1-S^-a+ (toℕ x) e α' β nz)
           (c1-eq Eq.refl (Eq.cong (₁₊ α' ,_)
             (Eq.trans (Eq.cong (β +_) (nsum-neg x (₁₊ α'))) Xeq0)))

  c₃eq : ((ract {0} ᵗ) (mk (e + - ₀) (₀ , ₁₊ y) (λ ())) (S^ ix)) .proj₂
         ≡ mk ((e + - ₀) + - (ix * Ky)) (₀ , ₁₊ y) (λ ())
  c₃eq = Eq.trans (ract1-S^-a0 (toℕ ix) (e + - ₀) y (λ ()))
           (c1-eq (Eq.cong ((e + - ₀) +_) (nsum-neg ix Ky)) Eq.refl)

  e₃ = (e + - ₀) + - (ix * Ky)

  xy≡-β : x * ₁₊ y ≡ - β
  xy≡-β = Eq.trans (Eq.cong (x *_) (Eq.sym eq-y))
          (Eq.trans (Eq.sym (-‿distribʳ-* x (₁₊ α')))
                    (Eq.cong -_ (Eq.sym beq)))

  c₅eq : ((ract {0} ᵗ) (mk (e₃ + - ₀) (₁₊ y , ₀) (λ ())) (S^ x)) .proj₂
         ≡ mk (e₃ + - ₀) (₁₊ y , ₁₊ g) (λ ())
  c₅eq = Eq.trans (ract1-S^-a+ (toℕ x) (e₃ + - ₀) y ₀ (λ ()))
           (c1-eq Eq.refl (Eq.cong (₁₊ y ,_)
             (Eq.trans (+-0ˡ _)
             (Eq.trans (nsum-neg x (₁₊ y))
             (Eq.trans (Eq.cong -_ xy≡-β)
             (Eq.trans (-‿involutive β) eq-g))))))

  ixβ≡α : ix * β ≡ ₁₊ α'
  ixβ≡α = Eq.trans (Eq.cong (ix *_) beq)
          (Eq.trans (Eq.sym (*-assoc ix x (₁₊ α')))
          (Eq.trans (Eq.cong (_* ₁₊ α') (lemma-⁻¹ˡ x {{instᵢ}}))
                    (*-identityˡ (₁₊ α'))))

  ab-eq : (₁₊ g , - ₁₊ y) ≡ (x * ₁₊ α' , ix * β)
  ab-eq = Eq.cong₂ _,_ (Eq.trans (Eq.sym eq-g) beq)
    (Eq.trans (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ α')))
              (Eq.sym ixβ≡α))

  iy-eq : ((₁₊ y , λ ()) ⁻¹) .proj₁ ≡ - iα
  iy-eq = Eq.trans (inv-cong (₁₊ y , λ ()) (-' (₁₊ α' , λ ())) (Eq.sym eq-y))
                   (inv-neg-comm (₁₊ α' , λ ()))

  ixKy : ix * Ky ≡ V
  ixKy = Eq.cong (ix *_)
    (Eq.trans (Eq.cong₂ _*_ iy-eq iy-eq) (negneg-* iα iα))

  αxα : ₁₊ α' * (x * ₁₊ α') ≡ x * (₁₊ α' * ₁₊ α')
  αxα = Eq.trans (Eq.sym (*-assoc (₁₊ α') x (₁₊ α')))
        (Eq.trans (Eq.cong (_* ₁₊ α') (*-comm (₁₊ α') x))
                  (*-assoc x (₁₊ α') (₁₊ α')))

  Kabyg : Kab y g ≡ - V
  Kabyg = KabV x* α' y g
    (Eq.trans (Eq.cong₂ _*_ (Eq.sym eq-y) (Eq.sym eq-g))
    (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ α') β))
    (Eq.cong -_ (Eq.trans (Eq.cong (₁₊ α' *_) beq) αxα))))

  e-fix : ((e₃ + - ₀) + - Kab y g) ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong (_+ - ₀) (Eq.cong ((e + - ₀) +_) (Eq.cong -_ ixKy)))
      (Eq.cong -_ Kabyg))
    (Eq.trans (Eq.cong (_+ - (- V)) (e+-0 ((e + - ₀) + - V)))
    (Eq.trans (cancel-+ (e + - ₀) V) (e+-0 e)))

-- Threading the M word, β = 0 branch (the middle box is (w , 0)).
ractM-b0 : ∀ (x* : ℤ* ₚ) (e : E) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀)) (w t : Fin (₁₊ p-2)) →
  β + - (x* .proj₁ * ₁₊ α') ≡ ₁₊ w →
  β ≡ ₀ →
  - ₁₊ w ≡ ₁₊ t →
  (nz' : (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) ≢ (₀ , ₀)) →
  ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (ZM x*)) .proj₂
  ≡ mk e (x* .proj₁ * ₁₊ α' , (x* ⁻¹) .proj₁ * β) nz'
ractM-b0 x* e α' β nz w t Xeq eq-b0 eq-t nz' =
  Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W5 .proj₂) c₁eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W3 .proj₂) c₃eq)
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W2 .proj₂)
              (c1-eq {e = e₂ + - ₀} {nz' = λ ()} Eq.refl (Eq.cong (₀ ,_) eq-t)))
  (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z W1 .proj₂) c₅eq)
            (c1-eq e-fix ab-eq))))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁
  instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}
  iα = ((₁₊ α' , λ ()) ⁻¹) .proj₁
  Kt = kS-a0 t (λ ())
  V  = ix * (iα * iα)

  W1 W2 W3 W5 : Circuit 1
  W1 = H
  W2 = S^ x • H
  W3 = H • W2
  W5 = H • (S^ ix • W3)

  c₁eq : ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (S^ x)) .proj₂
         ≡ mk e (₁₊ α' , ₁₊ w) (λ ())
  c₁eq = Eq.trans (ract1-S^-a+ (toℕ x) e α' β nz)
           (c1-eq Eq.refl (Eq.cong (₁₊ α' ,_)
             (Eq.trans (Eq.cong (β +_) (nsum-neg x (₁₊ α'))) Xeq)))

  e₂ = e + - Kab α' w

  c₃eq : ((ract {0} ᵗ) (mk e₂ (₁₊ w , - ₁₊ α') (λ ())) (S^ ix)) .proj₂
         ≡ mk e₂ (₁₊ w , ₀) (λ ())
  c₃eq = Eq.trans (ract1-S^-a+ (toℕ ix) e₂ w (- ₁₊ α') (λ ()))
           (c1-eq Eq.refl (Eq.cong (₁₊ w ,_)
             (Eq.trans (Eq.cong ((- ₁₊ α') +_) (nsum-neg ix (₁₊ w)))
             (Eq.trans (Eq.cong (λ z → - ₁₊ α' + - (ix * z)) (Eq.sym Xeq))
             (Eq.trans (valM-C x* (₁₊ α') β)
             (Eq.trans (Eq.cong (λ z → - (ix * z)) eq-b0)
             (Eq.trans (Eq.cong -_ (*-zeroʳ ix)) -0#≈0#)))))))

  c₅eq : ((ract {0} ᵗ) (mk (e₂ + - ₀) (₀ , ₁₊ t) (λ ())) (S^ x)) .proj₂
         ≡ mk ((e₂ + - ₀) + - (x * Kt)) (₀ , ₁₊ t) (λ ())
  c₅eq = Eq.trans (ract1-S^-a0 (toℕ x) (e₂ + - ₀) t (λ ()))
           (c1-eq (Eq.cong ((e₂ + - ₀) +_) (nsum-neg x Kt)) Eq.refl)

  t≡xα : ₁₊ t ≡ x * ₁₊ α'
  t≡xα = Eq.trans (Eq.sym eq-t)
         (Eq.trans (Eq.cong -_ (Eq.sym Xeq))
         (Eq.trans (Eq.cong -_ (Eq.cong (_+ - (x * ₁₊ α')) eq-b0))
         (Eq.trans (Eq.cong -_ (+-0ˡ (- (x * ₁₊ α'))))
                   (-‿involutive (x * ₁₊ α')))))

  ab-eq : (₁₊ t , ₀) ≡ (x * ₁₊ α' , ix * β)
  ab-eq = Eq.cong₂ _,_ t≡xα
    (Eq.sym (Eq.trans (Eq.cong (ix *_) eq-b0) (*-zeroʳ ix)))

  it-eq : ((₁₊ t , λ ()) ⁻¹) .proj₁ ≡ ix * iα
  it-eq = Eq.trans
    (inv-cong (₁₊ t , λ ()) (x* *' (₁₊ α' , λ ())) t≡xα)
    (inv-distrib x* (₁₊ α' , λ ()))

  xKt-V : x * Kt ≡ V
  xKt-V = Eq.trans (Eq.cong (x *_) (Eq.cong₂ _*_ it-eq it-eq))
    (Eq.trans (Eq.sym (*-assoc x (ix * iα) (ix * iα)))
    (Eq.trans (Eq.cong (_* (ix * iα))
      (Eq.trans (Eq.sym (*-assoc x ix iα))
      (Eq.trans (Eq.cong (_* iα) (lemma-⁻¹ʳ x {{instᵢ}}))
                (*-identityˡ iα))))
    (Eq.trans (Eq.sym (*-assoc iα ix iα))
    (Eq.trans (Eq.cong (_* iα) (*-comm iα ix))
              (*-assoc ix iα iα)))))

  αxα : ₁₊ α' * (x * ₁₊ α') ≡ x * (₁₊ α' * ₁₊ α')
  αxα = Eq.trans (Eq.sym (*-assoc (₁₊ α') x (₁₊ α')))
        (Eq.trans (Eq.cong (_* ₁₊ α') (*-comm (₁₊ α') x))
                  (*-assoc x (₁₊ α') (₁₊ α')))

  KabW-V : Kab α' w ≡ - V
  KabW-V = KabV x* α' α' w
    (Eq.trans (Eq.cong (₁₊ α' *_)
      (Eq.trans (Eq.sym Xeq)
      (Eq.trans (Eq.cong (_+ - (x * ₁₊ α')) eq-b0)
                (+-0ˡ (- (x * ₁₊ α'))))))
    (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ α') (x * ₁₊ α')))
              (Eq.cong -_ αxα)))

  e-fix : (((e₂ + - ₀) + - (x * Kt)) + - ₀) ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong₂ _+_ (Eq.cong (λ z → (e + - z) + - ₀) KabW-V)
                    (Eq.cong -_ xKt-V))
      Eq.refl)
    (Eq.trans (e+-0 _)
    (Eq.trans (Eq.cong (_+ - V) (e+-0 (e + - (- V))))
              (cancel-+' e V)))

-- Multiplication by a unit is injective at ₀.
x*cancel : ∀ (x* : ℤ* ₚ) (a : ℤ ₚ) → x* .proj₁ * a ≡ ₀ → a ≡ ₀
x*cancel x* a e0 =
  Eq.trans
    (Eq.sym (Eq.trans (Eq.sym (*-assoc ((x* ⁻¹) .proj₁) (x* .proj₁) a))
            (Eq.trans (Eq.cong (_* a)
                        (lemma-⁻¹ˡ (x* .proj₁)
                          {{nztoℕ {y = x* .proj₁} {neq0 = x* .proj₂}}}))
                      (*-identityˡ a))))
    (Eq.trans (Eq.cong ((x* ⁻¹) .proj₁ *_) e0) (*-zeroʳ ((x* ⁻¹) .proj₁)))

-- The M-image of a nonzero A value is nonzero.
Mact-nz : ∀ (x* : ℤ* ₚ) (ab : ℤ ₚ × ℤ ₚ) → ab ≢ (₀ , ₀) →
  (x* .proj₁ * ab .proj₁ , (x* ⁻¹) .proj₁ * ab .proj₂) ≢ (₀ , ₀)
Mact-nz x* ab nz e0 = nz (Eq.cong₂ _,_
  (x*cancel x* (ab .proj₁) (Eq.cong proj₁ e0))
  (x*cancel (x* ⁻¹) (ab .proj₂) (Eq.cong proj₂ e0)))

-- Threading the M word, all branches: the width-1 coset action of M x
-- is (e , (α , β)) ↦ (e , (x·α , x⁻¹·β)).
ractM! : ∀ (x* : ℤ* ₚ) (e : E) (ab : ℤ ₚ × ℤ ₚ) (nz : ab ≢ (₀ , ₀))
  (nz' : (x* .proj₁ * ab .proj₁ , (x* ⁻¹) .proj₁ * ab .proj₂) ≢ (₀ , ₀)) →
  ((ract {0} ᵗ) (mk e ab nz) (ZM x*)) .proj₂
  ≡ mk e (x* .proj₁ * ab .proj₁ , (x* ⁻¹) .proj₁ * ab .proj₂) nz'
ractM! x* e (₀ , ₀) nz nz' = ⊥-elim (nz auto)
ractM! x* e (₀ , ₁₊ β') nz nz' =
  elim-suc (- ((x* ⁻¹) .proj₁ * ₁₊ β'))
           (neg≢0 ((x* ⁻¹) .proj₁ * ₁₊ β')
                  (((x* ⁻¹) *' (₁₊ β' , λ ())) .proj₂))
    λ u eq-u →
  Eq.trans
    (ractM-0b x* e β' nz u eq-u
      (λ e0 → ((x* ⁻¹) *' (₁₊ β' , λ ())) .proj₂ (Eq.cong proj₂ e0)))
    (c1-eq Eq.refl
      (Eq.cong (_, (x* ⁻¹) .proj₁ * ₁₊ β') (Eq.sym (*-zeroʳ (x* .proj₁)))))
ractM! x* e (₁₊ α' , β) nz nz' =
  elim-fin (β + - (x* .proj₁ * ₁₊ α'))
    (λ Xeq0 →
       elim-suc (- ₁₊ α') (neg≢0 (₁₊ α') λ ()) λ y eq-y →
       elim-suc β
         (λ e0 → (x* *' (₁₊ α' , λ ())) .proj₂
                   (Eq.trans (Eq.sym (+-‿cancel β (x* .proj₁ * ₁₊ α') Xeq0)) e0))
         λ g eq-g →
       ractM-w0 x* e α' β nz y g Xeq0 eq-y eq-g nz')
    (λ w Xeq →
       elim-fin β
         (λ eq-b0 →
            elim-suc (- ₁₊ w) (neg≢0 (₁₊ w) λ ()) λ t eq-t →
            ractM-b0 x* e α' β nz w t Xeq eq-b0 eq-t nz')
         (λ g eq-g →
            elim-suc (- ((x* ⁻¹) .proj₁ * β))
              (neg≢0 ((x* ⁻¹) .proj₁ * β)
                (((x* ⁻¹) *' (β , (λ e0 → suc≢0 (Eq.trans (Eq.sym eq-g) e0))))
                  .proj₂))
              λ v eq-v →
            elim-suc (x* .proj₁ * ₁₊ α') ((x* *' (₁₊ α' , λ ())) .proj₂)
              λ s eq-s →
            ractM-nn x* e α' β nz w v s g Xeq eq-v eq-s eq-g nz'))

-- semi-MS at width 1: M x then S against S^(x²) then M x.  On an a = 0
-- box both sides subtract x²·β⁻² from the E box; on an a ≠ 0 box both
-- leave E fixed and agree on the value by ix·(β − x²α) ≡ ix·β − xα.
semi-MS-0b : ∀ (x* : ℤ* ₚ) (e : E) (β' : Fin (₁₊ p-2))
  (nz : (₀ , ₁₊ β') ≢ (₀ , ₀)) (m : Fin (₁₊ p-2)) →
  (x* ⁻¹) .proj₁ * ₁₊ β' ≡ ₁₊ m →
  ((ract {0} ᵗ) (mk e (₀ , ₁₊ β') nz) (ZM x* • S)) .proj₂
  ≡ ((ract {0} ᵗ) (mk e (₀ , ₁₊ β') nz) (S^ (x* ^2) • ZM x*)) .proj₂
semi-MS-0b x* e β' nz m eq-m =
  Eq.trans
    (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z S .proj₂)
                (ractM! x* e (₀ , ₁₊ β') nz nzM))
      (c1-eq
        (Eq.cong (λ v → e + - v)
          (Eq.trans (kS-cong {the-A} {(₀ , ₁₊ m) , (λ ())} valAB) im²x))
        (Eq.trans (a'S-cong {the-A} {(₀ , ₁₊ m) , (λ ())} valAB)
          (Eq.cong₂ _,_ (Eq.sym (*-zeroʳ (x* .proj₁))) (Eq.sym eq-m)))))
    (Eq.sym
      (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z (ZM x*) .proj₂) rw0)
        (ractM! x* (e + - ((x* ^2) * K0)) (₀ , ₁₊ β') nz nzM)))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁
  instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}
  iβ = ((₁₊ β' , λ ()) ⁻¹) .proj₁
  K0 = kS-a0 β' nz
  nzM = Mact-nz x* (₀ , ₁₊ β') nz

  the-A : A
  the-A = (x * ₀ , ix * ₁₊ β') , nzM

  valAB : (x * ₀ , ix * ₁₊ β') ≡ (₀ , ₁₊ m)
  valAB = Eq.cong₂ _,_ (*-zeroʳ x) eq-m

  im-eq : ((₁₊ m , λ ()) ⁻¹) .proj₁ ≡ x * iβ
  im-eq = Eq.trans
    (inv-cong (₁₊ m , λ ()) ((x* ⁻¹) *' (₁₊ β' , λ ())) (Eq.sym eq-m))
    (Eq.trans (inv-distrib (x* ⁻¹) (₁₊ β' , λ ()))
              (Eq.cong (_* iβ) (inv-involutive x*)))

  im²x : kS ((₀ , ₁₊ m) , (λ ())) ≡ (x* ^2) * K0
  im²x = Eq.trans (Eq.cong₂ _*_ im-eq im-eq)
    (Eq.trans (*-assoc x iβ (x * iβ))
    (Eq.trans (Eq.cong (x *_) (Eq.sym (*-assoc iβ x iβ)))
    (Eq.trans (Eq.cong (λ z → x * (z * iβ)) (*-comm iβ x))
    (Eq.trans (Eq.cong (x *_) (*-assoc x iβ iβ))
              (Eq.sym (*-assoc x x (iβ * iβ)))))))

  rw0 : ((ract {0} ᵗ) (mk e (₀ , ₁₊ β') nz) (S^ (x* ^2))) .proj₂
        ≡ mk (e + - ((x* ^2) * K0)) (₀ , ₁₊ β') nz
  rw0 = Eq.trans (ract1-S^-a0 (toℕ (x* ^2)) e β' nz)
          (c1-eq (Eq.cong (e +_) (nsum-neg (x* ^2) K0)) Eq.refl)

semi-MS-nn : ∀ (x* : ℤ* ₚ) (e : E) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ)
  (nz : (₁₊ α' , β) ≢ (₀ , ₀)) (s : Fin (₁₊ p-2)) →
  x* .proj₁ * ₁₊ α' ≡ ₁₊ s →
  ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (ZM x* • S)) .proj₂
  ≡ ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (S^ (x* ^2) • ZM x*)) .proj₂
semi-MS-nn x* e α' β nz s eq-s =
  Eq.trans
    (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z S .proj₂)
                (ractM! x* e (₁₊ α' , β) nz nzM))
      (c1-eq
        (Eq.trans (Eq.cong (λ v → e + - v)
           (Eq.trans (kS-cong {the-A} {(₁₊ s , ix * β) , (λ ())} valAB)
                     (kS-a+ s (ix * β) (λ ()))))
           (e+-0 e))
        (Eq.trans (a'S-cong {the-A} {(₁₊ s , ix * β) , (λ ())} valAB)
          (Eq.trans (a'S-a+ s (ix * β) (λ ()))
            (Eq.cong₂ _,_ (Eq.sym eq-s)
              (Eq.trans (Eq.cong ((ix * β) +_) (Eq.cong -_ (Eq.sym eq-s)))
                        (Eq.sym ixB2)))))))
    (Eq.sym
      (Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z (ZM x*) .proj₂) rwA)
        (ractM! x* e (₁₊ α' , B2) (λ ())
          (Mact-nz x* (₁₊ α' , B2) (λ ())))))
  where
  x  = x* .proj₁
  ix = (x* ⁻¹) .proj₁
  instᵢ = nztoℕ {y = x} {neq0 = x* .proj₂}
  nzM = Mact-nz x* (₁₊ α' , β) nz
  B2 = β + - ((x* ^2) * ₁₊ α')

  the-A : A
  the-A = (x * ₁₊ α' , ix * β) , nzM

  valAB : (x * ₁₊ α' , ix * β) ≡ (₁₊ s , ix * β)
  valAB = Eq.cong (_, ix * β) eq-s

  ixB2 : ix * B2 ≡ (ix * β) + - (x * ₁₊ α')
  ixB2 = Eq.trans (*-distribˡ-+ ix β (- ((x* ^2) * ₁₊ α')))
    (Eq.cong ((ix * β) +_)
      (Eq.trans (Eq.sym (-‿distribʳ-* ix ((x* ^2) * ₁₊ α')))
      (Eq.cong -_
        (Eq.trans (Eq.sym (*-assoc ix (x * x) (₁₊ α')))
          (Eq.cong (_* ₁₊ α')
            (Eq.trans (Eq.sym (*-assoc ix x x))
            (Eq.trans (Eq.cong (_* x) (lemma-⁻¹ˡ x {{instᵢ}}))
                      (*-identityˡ x))))))))

  rwA : ((ract {0} ᵗ) (mk e (₁₊ α' , β) nz) (S^ (x* ^2))) .proj₂
        ≡ mk e (₁₊ α' , B2) (λ ())
  rwA = Eq.trans (ract1-S^-a+ (toℕ (x* ^2)) e α' β nz)
          (c1-eq Eq.refl (Eq.cong (₁₊ α' ,_)
            (Eq.cong (β +_) (nsum-neg (x* ^2) (₁₊ α')))))
