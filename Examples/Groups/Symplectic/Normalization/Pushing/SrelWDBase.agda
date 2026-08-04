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

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise)
open import Data.Sum using (inj₁ ; inj₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.Normalization.Pushing.PushML p-2 p-prime as PushML
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (dir-of-DS ; d-of-DS)
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (S^-↓ᵏ ; ↑↓ᵏ-comm)
import Relation.Binary.Reasoning.Setoid as SR
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Data.Nat using (zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (_%_ ; m%n<n ; %-distribˡ-+ ; m*n%n≡0 ; m<n⇒m%n≡m ; m%n%n≡m%n)
open import Data.Product using (∃)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ<)
import Data.Nat.Properties as NP
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (A-dir-S-power)
import Examples.Groups.Symplectic.BR.One.A p-2 p-prime as OA
private variable
  n : ℕ

C = ML

ract : ∀ {n} → C (₁₊ n) → Gen (₁₊ n) → Circuit n × C (₁₊ n)
ract = PushML.ract

infix 4 _≋_
_≋_ : Rel (Circuit n × C (₁₊ n)) 0ℓ
_≋_ {n} = Pointwise (PB._≈_ (n QRel,_===_)) (_≡_ {A = C (₁₊ n)})

-- Iterate an endo.
it : ∀ {Q : Set} → (Q → Q) → ℕ → Q → Q
it f zero    d = d
it f (suc n) d = it f n (f d)

------------------------------------------------------------------------
-- Additive order of ℤ/p: summing p copies of any x gives 0.

nsum : ℕ → ℤ ₚ → ℤ ₚ
nsum zero    x = ₀
nsum (suc k) x = x + nsum k x

toℕ-+ : ∀ (x y : ℤ ₚ) → toℕ (x + y) ≡ (toℕ x +ℕ toℕ y) % p
toℕ-+ x y = toℕ-fromℕ< (m%n<n (toℕ x +ℕ toℕ y) p)

nsum-toℕ : ∀ (k : ℕ) (x : ℤ ₚ) → toℕ (nsum k x) ≡ (k *ℕ toℕ x) % p
nsum-toℕ zero    x = Eq.sym (m<n⇒m%n≡m (NP.0<1+n {p-1}))
nsum-toℕ (suc k) x = Eq.trans (toℕ-+ x (nsum k x))
  (Eq.trans (Eq.cong (λ z → (toℕ x +ℕ z) % p) (nsum-toℕ k x)) reduce)
  where
  reduce : (toℕ x +ℕ (k *ℕ toℕ x) % p) % p ≡ (suc k *ℕ toℕ x) % p
  reduce = Eq.trans (%-distribˡ-+ (toℕ x) ((k *ℕ toℕ x) % p) p)
           (Eq.trans (Eq.cong (λ z → (toℕ x % p +ℕ z) % p) (m%n%n≡m%n (k *ℕ toℕ x) p))
                     (Eq.sym (%-distribˡ-+ (toℕ x) (k *ℕ toℕ x) p)))

nsum-p≡0 : ∀ (x : ℤ ₚ) → nsum p x ≡ ₀
nsum-p≡0 x = toℕ-injective
  (Eq.trans (nsum-toℕ p x)
  (Eq.trans (Eq.cong (_% p) (NP.*-comm p (toℕ x)))
            (m*n%n≡0 (toℕ x) p)))

------------------------------------------------------------------------
-- d-of-DS iterated: the a-component is invariant, the b-component
-- accumulates -a; after p steps it returns to the start (nsum-p≡0).

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥-elim)

it-dDS-a0 : ∀ (k : ℕ) (b : ℤ ₚ) → it d-of-DS k (₀ , b) ≡ (₀ , b)
it-dDS-a0 zero    b = Eq.refl
it-dDS-a0 (suc k) b = it-dDS-a0 k b

dDS-a+ : ∀ (x b : ℤ ₚ) → x ≢ ₀ → d-of-DS (x , b) ≡ (x , b + - x)
dDS-a+ ₀      b nz = ⊥-elim (nz Eq.refl)
dDS-a+ (₁₊ a) b nz = Eq.refl

it-dDS-nz : ∀ (k : ℕ) (x b : ℤ ₚ) → x ≢ ₀ →
  it d-of-DS k (x , b) ≡ (x , b + nsum k (- x))
it-dDS-nz zero    x b nz = Eq.cong (x ,_) (Eq.sym (+-identityʳ b))
it-dDS-nz (suc k) x b nz =
  Eq.trans (Eq.cong (it d-of-DS k) (dDS-a+ x b nz))
  (Eq.trans (it-dDS-nz k x (b + - x) nz)
            (Eq.cong (x ,_) (+-assoc b (- x) (nsum k (- x)))))

dDS^p≡id : ∀ (d : D) → it d-of-DS p d ≡ d
dDS^p≡id (₀ , b)      = it-dDS-a0 p b
dDS^p≡id (x@(₁₊ a) , b) = Eq.trans (it-dDS-nz p x b (λ ()))
  (Eq.cong (x ,_) (Eq.trans (Eq.cong (b +_) (nsum-p≡0 (- x))) (+-identityʳ b)))

------------------------------------------------------------------------
-- order-S inj₂ residual: an a=0 box escapes an S each step (⇒ S^k), an
-- a≠0 box escapes nothing (⇒ ε).

dirDS-a+ : ∀ {j} (d : D) → proj₁ d ≢ ₀ → dir-of-DS {j} d ≡ ε
dirDS-a+ (₀ , b)    nz = ⊥-elim (nz Eq.refl)
dirDS-a+ (₁₊ a , b) nz = Eq.refl

dDS-nz : ∀ (d : D) → proj₁ d ≢ ₀ → proj₁ (d-of-DS d) ≢ ₀
dDS-nz (₀ , b)    nz = ⊥-elim (nz Eq.refl)
dDS-nz (₁₊ a , b) nz = λ ()

ract-S^-resid-a0 : ∀ {m} (b : ℤ ₚ) (lm : C (₁₊ m)) (k : ℕ) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , b) , lm)) (S ^ k)) .proj₁ ≡ S ^ k
ract-S^-resid-a0 b lm zero          = Eq.refl
ract-S^-resid-a0 b lm (suc zero)    = Eq.refl
ract-S^-resid-a0 b lm (suc (suc k)) = Eq.cong (S •_) (ract-S^-resid-a0 b lm (suc k))

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)

  ract-S^-resid-a+ : ∀ (d : D) (lm : C (₁₊ m)) (k : ℕ) → proj₁ d ≢ ₀ →
    ((ract {₁₊ m} ᵗ) (inj₂ (d , lm)) (S ^ k)) .proj₁ ≈ ε
  ract-S^-resid-a+ d lm zero       nz = refl
  ract-S^-resid-a+ d lm (suc zero) nz = refl' (dirDS-a+ d nz)
  ract-S^-resid-a+ d lm (suc (suc k)) nz =
    trans (cong (refl' (dirDS-a+ d nz))
                (ract-S^-resid-a+ (d-of-DS d) lm (suc k) (dDS-nz d nz)))
          left-unit

------------------------------------------------------------------------
-- order-S engine: threading S^k through an inj₂ coset cycles the bottom
-- D-box via d-of-DS, leaving the lifted tail lm fixed.

ract-S^-coset : ∀ {m} (d : D) (lm : C (₁₊ m)) (k : ℕ) →
  ((ract {₁₊ m} ᵗ) (inj₂ (d , lm)) (S ^ k)) .proj₂ ≡ inj₂ (it d-of-DS k d , lm)
ract-S^-coset d lm zero          = Eq.refl
ract-S^-coset d lm (suc zero)    = Eq.refl
ract-S^-coset d lm (suc (suc k)) = ract-S^-coset (d-of-DS d) lm (suc k)

------------------------------------------------------------------------
-- Width-1 machinery.  At width 1 the coset action is the direct A/E-box
-- update of Push.ract (the residual is always ε), so every axiom case
-- reduces to an orbit computation on (e , a) plus the collapse of
-- Circuit 0 residuals.  The A-box nonzeroness proofs are judgementally
-- irrelevant (⊥ is an irrelevant record), so only value components
-- matter in the coset equalities.

-- Every width-0 word collapses to ε (Gen 0 is empty).
sing0 : {w : Circuit 0} → PB._≈_ (0 QRel,_===_) w ε
sing0 {[ () ]ʷ}
sing0 {ε}     = PB.refl
sing0 {w • v} = PB.trans (PB.cong sing0 sing0) PB.left-unit

-- Width-1 coset builder and its congruence.
mk : E → (ab : ℤ ₚ × ℤ ₚ) → ab ≢ (₀ , ₀) → C 1
mk e ab nz = ([] , e) , ([] , (ab , nz))

c1-eq : ∀ {e e' ab ab'} {nz : ab ≢ (₀ , ₀)} {nz' : ab' ≢ (₀ , ₀)} →
  e ≡ e' → ab ≡ ab' → mk e ab nz ≡ mk e' ab' nz'
c1-eq Eq.refl Eq.refl = Eq.refl

e+-0 : ∀ (e : E) → e + - ₀ ≡ e
e+-0 e = Eq.trans (Eq.cong (e +_) -0#≈0#) (+-identityʳ e)

gS gH : Gen 1
gS = gate₁ S-gate
gH = gate₁ H-gate

-- A nonzero element is a successor, and negation preserves nonzeroness.
x≢0⇒suc : ∀ (x : ℤ ₚ) → x ≢ ₀ → ∃ λ y → x ≡ ₁₊ y
x≢0⇒suc ₀      nz = ⊥-elim (nz auto)
x≢0⇒suc (₁₊ y) nz = y , Eq.refl

-- Continuation-style variant: cheaper than `with`, which would abstract
-- the scrutinee over the (large, partially stuck) traversal goals.
elim-suc : ∀ (x : ℤ ₚ) → x ≢ ₀ → {A : Set} → (∀ y → x ≡ ₁₊ y → A) → A
elim-suc ₀      nz k = ⊥-elim (nz auto)
elim-suc (₁₊ y) nz k = k y Eq.refl

neg≢0 : ∀ (x : ℤ ₚ) → x ≢ ₀ → (- x) ≢ ₀
neg≢0 x nz eq =
  nz (Eq.trans (Eq.sym (-‿involutive x)) (Eq.trans (Eq.cong -_ eq) -0#≈0#))

-- Congruence of the threaded action in the coset, and substitution on
-- the left of ≋ — used to rewrite stuck A-box values (negated
-- components) into constructor form mid-orbit.
ract-cong : ∀ {c c' : C 1} (w : Circuit 1) → c ≡ c' →
  (ract {0} ᵗ) c w ≡ (ract {0} ᵗ) c' w
ract-cong w Eq.refl = Eq.refl

≋-substˡ : ∀ {n} {x y z : Circuit n × C (₁₊ n)} → x ≡ y → _≋_ {n} y z → x ≋ z
≋-substˡ Eq.refl pf = pf

-- The S-escape power of an A box: b⁻² on an a = 0 box, ₀ on an a ≠ 0 box.
kS-a0 : ∀ (b' : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b') ≢ (₀ , ₀)) → ℤ ₚ
kS-a0 b' nz = A-dir-S-power ((₀ , ₁₊ b') , nz) gS tt .proj₁

kS-a+ : ∀ (a' : Fin (₁₊ p-2)) (b : ℤ ₚ) (nz : (₁₊ a' , b) ≢ (₀ , ₀)) →
  A-dir-S-power ((₁₊ a' , b) , nz) gS tt .proj₁ ≡ ₀
kS-a+ a' ₀      nz = Eq.refl
kS-a+ a' (₁₊ _) nz = Eq.refl

-- The width-1 H-step on the A box, as value maps: the updated A value
-- and the escape power.  Both are invariant in the (judgementally
-- irrelevant) nonzeroness proof, and congruent in the A value — the
-- congruences let us rewrite stuck (negated) values into constructor
-- form so that the next step computes.
a'H : A → ℤ ₚ × ℤ ₚ
a'H a = OA.dir-and-A'-of 0 a gH tt .proj₂ .proj₁

kH : A → ℤ ₚ
kH a = A-dir-S-power a gH tt .proj₁

a'H-cong : {x y : A} → x .proj₁ ≡ y .proj₁ → a'H x ≡ a'H y
a'H-cong {xv , xnz} {yv , ynz} Eq.refl = Eq.refl

kH-cong : {x y : A} → x .proj₁ ≡ y .proj₁ → kH x ≡ kH y
kH-cong {xv , xnz} {yv , ynz} Eq.refl = Eq.refl

-- The width-1 S-step value maps and congruences.
a'S : A → ℤ ₚ × ℤ ₚ
a'S a = OA.dir-and-A'-of 0 a gS tt .proj₂ .proj₁

a'S-cong : {x y : A} → x .proj₁ ≡ y .proj₁ → a'S x ≡ a'S y
a'S-cong {xv , xnz} {yv , ynz} Eq.refl = Eq.refl

kS : A → ℤ ₚ
kS a = A-dir-S-power a gS tt .proj₁

kS-cong : {x y : A} → x .proj₁ ≡ y .proj₁ → kS x ≡ kS y
kS-cong {xv , xnz} {yv , ynz} Eq.refl = Eq.refl

-- The S value update on an a ≠ 0 box, uniformly in b (the case tree
-- splits b before the gate, so this needs its own b-split).
a'S-a+ : ∀ (a' : Fin (₁₊ p-2)) (b : ℤ ₚ) (nzp : (₁₊ a' , b) ≢ (₀ , ₀)) →
  a'S ((₁₊ a' , b) , nzp) ≡ (₁₊ a' , b + - ₁₊ a')
a'S-a+ a' ₀      nzp = Eq.refl
a'S-a+ a' (₁₊ _) nzp = Eq.refl

-- Total zero/successor split (continuation-style, like elim-suc).
elim-fin : ∀ (x : ℤ ₚ) {A : Set} →
  (x ≡ ₀ → A) → (∀ w → x ≡ ₁₊ w → A) → A
elim-fin ₀      k0 ks = k0 Eq.refl
elim-fin (₁₊ w) k0 ks = ks w Eq.refl

-- Small ring helpers used by the orbit computations.
+-0ˡ : ∀ (x : ℤ ₚ) → ₀ + x ≡ x
+-0ˡ x = Eq.trans (+-comm ₀ x) (+-identityʳ x)

cancel-+ : ∀ (x v : ℤ ₚ) → (x + - v) + - (- v) ≡ x
cancel-+ x v = Eq.trans (+-assoc x (- v) (- (- v)))
  (Eq.trans (Eq.cong (x +_) (+-inverseʳ (- v))) (+-identityʳ x))

cancel-+' : ∀ (x v : ℤ ₚ) → (x + - (- v)) + - v ≡ x
cancel-+' x v = Eq.trans (+-assoc x (- (- v)) (- v))
  (Eq.trans (Eq.cong (x +_) (+-inverseˡ (- v))) (+-identityʳ x))

negneg-* : ∀ (u v : ℤ ₚ) → (- u) * (- v) ≡ u * v
negneg-* u v = Eq.trans (Eq.sym (-‿distribˡ-* u (- v)))
  (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* u v))) (-‿involutive (u * v)))

+-‿cancel : ∀ (x y : ℤ ₚ) → x + - y ≡ ₀ → x ≡ y
+-‿cancel x y eq = Eq.trans (Eq.sym (+-identityʳ x))
  (Eq.trans (Eq.cong (x +_) (Eq.sym (+-inverseˡ y)))
  (Eq.trans (Eq.sym (+-assoc x (- y) y))
  (Eq.trans (Eq.cong (_+ y) eq) (+-0ˡ y))))

-- The H escape power on a fully nonzero box, as an inverse value, and
-- its behaviour under negating one factor.
Kab : (a₀ b₀ : Fin (₁₊ p-2)) → ℤ ₚ
Kab a₀ b₀ = (((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())) ⁻¹) .proj₁

Kab-neg : ∀ (a₀ b₀ y : Fin (₁₊ p-2)) → ₁₊ y ≡ - (₁₊ a₀) →
  Kab b₀ y ≡ - Kab a₀ b₀
Kab-neg a₀ b₀ y yeq = Eq.trans
  (inv-cong ((₁₊ b₀ , λ ()) *' (₁₊ y , λ ()))
            (-' ((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())))
    (Eq.trans (Eq.cong (₁₊ b₀ *_) yeq)
      (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ b₀) (₁₊ a₀)))
                (Eq.cong -_ (*-comm (₁₊ b₀) (₁₊ a₀))))))
  (inv-neg-comm ((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())))

Kab-comm : ∀ (a₀ b₀ : Fin (₁₊ p-2)) → Kab a₀ b₀ ≡ Kab b₀ a₀
Kab-comm a₀ b₀ = inv-cong ((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ()))
                          ((₁₊ b₀ , λ ()) *' (₁₊ a₀ , λ ()))
                          (*-comm (₁₊ a₀) (₁₊ b₀))

Kab-yy : ∀ (a₀ y : Fin (₁₊ p-2)) → ₁₊ y ≡ - (₁₊ a₀) → Kab y y ≡ Kab a₀ a₀
Kab-yy a₀ y yeq = inv-cong ((₁₊ y , λ ()) *' (₁₊ y , λ ()))
                           ((₁₊ a₀ , λ ()) *' (₁₊ a₀ , λ ()))
                    (Eq.trans (Eq.cong₂ _*_ yeq yeq) (negneg-* (₁₊ a₀) (₁₊ a₀)))

-- The partial-fraction identity (bw)⁻¹ + (ba)⁻¹ ≡ (aw)⁻¹ for a + w ≡ b,
-- the phase bookkeeping of the (S•H)³ orbit on a fully nonzero box.
pf-inv : ∀ (a₀ w b₀ : Fin (₁₊ p-2)) → ₁₊ a₀ + ₁₊ w ≡ ₁₊ b₀ →
  Kab b₀ w + Kab b₀ a₀ ≡ Kab a₀ w
pf-inv a₀ w b₀ awb = begin
  Kab b₀ w + Kab b₀ a₀        ≡⟨ Eq.cong₂ _+_ (inv-distrib B* W*) (inv-distrib B* A*) ⟩
  ib * iw + ib * ia           ≡⟨ Eq.sym (*-distribˡ-+ ib iw ia) ⟩
  ib * (iw + ia)              ≡⟨ Eq.cong (ib *_) iwia ⟩
  ib * ((ia * iw) * ₁₊ b₀)    ≡⟨ Eq.sym (*-assoc ib (ia * iw) (₁₊ b₀)) ⟩
  (ib * (ia * iw)) * ₁₊ b₀    ≡⟨ Eq.cong (_* ₁₊ b₀) (*-comm ib (ia * iw)) ⟩
  ((ia * iw) * ib) * ₁₊ b₀    ≡⟨ *-assoc (ia * iw) ib (₁₊ b₀) ⟩
  (ia * iw) * (ib * ₁₊ b₀)    ≡⟨ Eq.cong ((ia * iw) *_)
                                   (lemma-⁻¹ˡ (₁₊ b₀) {{nztoℕ {y = ₁₊ b₀} {neq0 = λ ()}}}) ⟩
  (ia * iw) * ₁               ≡⟨ *-identityʳ (ia * iw) ⟩
  ia * iw                     ≡⟨ Eq.sym (inv-distrib A* W*) ⟩
  Kab a₀ w ∎
  where
  open Eq.≡-Reasoning
  A* W* B* : ℤ* ₚ
  A* = (₁₊ a₀ , λ ())
  W* = (₁₊ w , λ ())
  B* = (₁₊ b₀ , λ ())
  ia = (A* ⁻¹) .proj₁
  iw = (W* ⁻¹) .proj₁
  ib = (B* ⁻¹) .proj₁

  p1 : (ia * iw) * ₁₊ a₀ ≡ iw
  p1 = Eq.trans (*-assoc ia iw (₁₊ a₀))
       (Eq.trans (Eq.cong (ia *_) (*-comm iw (₁₊ a₀)))
       (Eq.trans (Eq.sym (*-assoc ia (₁₊ a₀) iw))
       (Eq.trans (Eq.cong (_* iw)
                   (lemma-⁻¹ˡ (₁₊ a₀) {{nztoℕ {y = ₁₊ a₀} {neq0 = λ ()}}}))
                 (*-identityˡ iw))))

  p2 : (ia * iw) * ₁₊ w ≡ ia
  p2 = Eq.trans (*-assoc ia iw (₁₊ w))
       (Eq.trans (Eq.cong (ia *_)
                   (lemma-⁻¹ˡ (₁₊ w) {{nztoℕ {y = ₁₊ w} {neq0 = λ ()}}}))
                 (*-identityʳ ia))

  iwia : iw + ia ≡ (ia * iw) * ₁₊ b₀
  iwia = Eq.sym (Eq.trans (Eq.cong ((ia * iw) *_) (Eq.sym awb))
         (Eq.trans (*-distribˡ-+ (ia * iw) (₁₊ a₀) (₁₊ w))
                   (Eq.cong₂ _+_ p1 p2)))

-- The x-scaled partial fraction x·(wg)⁻¹ + (ag)⁻¹ ≡ (aw)⁻¹ for
-- x·a + w ≡ g — the phase bookkeeping of the generic M-word orbit.
pf-invx : ∀ (x* : ℤ* ₚ) (a₀ w g : Fin (₁₊ p-2)) →
  x* .proj₁ * ₁₊ a₀ + ₁₊ w ≡ ₁₊ g →
  x* .proj₁ * Kab w g + Kab a₀ g ≡ Kab a₀ w
pf-invx x* a₀ w g awb = begin
  x * Kab w g + Kab a₀ g      ≡⟨ Eq.cong₂ _+_ (Eq.cong (x *_) (inv-distrib W* G*))
                                              (inv-distrib A* G*) ⟩
  x * (iw * ig) + ia * ig     ≡⟨ Eq.cong (_+ ia * ig) (Eq.sym (*-assoc x iw ig)) ⟩
  (x * iw) * ig + ia * ig     ≡⟨ Eq.sym (*-distribʳ-+ ig (x * iw) ia) ⟩
  (x * iw + ia) * ig          ≡⟨ Eq.cong (_* ig) key ⟩
  ((ia * iw) * ₁₊ g) * ig     ≡⟨ *-assoc (ia * iw) (₁₊ g) ig ⟩
  (ia * iw) * (₁₊ g * ig)     ≡⟨ Eq.cong ((ia * iw) *_)
                                   (Eq.trans (*-comm (₁₊ g) ig)
                                     (lemma-⁻¹ˡ (₁₊ g) {{nztoℕ {y = ₁₊ g} {neq0 = λ ()}}})) ⟩
  (ia * iw) * ₁               ≡⟨ *-identityʳ (ia * iw) ⟩
  ia * iw                     ≡⟨ Eq.sym (inv-distrib A* W*) ⟩
  Kab a₀ w ∎
  where
  open Eq.≡-Reasoning
  x = x* .proj₁
  A* W* G* : ℤ* ₚ
  A* = (₁₊ a₀ , λ ())
  W* = (₁₊ w , λ ())
  G* = (₁₊ g , λ ())
  ia = (A* ⁻¹) .proj₁
  iw = (W* ⁻¹) .proj₁
  ig = (G* ⁻¹) .proj₁

  p1x : (ia * iw) * (x * ₁₊ a₀) ≡ x * iw
  p1x = Eq.trans (*-comm (ia * iw) (x * ₁₊ a₀))
        (Eq.trans (*-assoc x (₁₊ a₀) (ia * iw))
        (Eq.trans (Eq.cong (x *_) (Eq.sym (*-assoc (₁₊ a₀) ia iw)))
        (Eq.trans (Eq.cong (λ z → x * (z * iw))
                    (Eq.trans (*-comm (₁₊ a₀) ia)
                      (lemma-⁻¹ˡ (₁₊ a₀) {{nztoℕ {y = ₁₊ a₀} {neq0 = λ ()}}})))
                  (Eq.cong (x *_) (*-identityˡ iw)))))

  p2x : (ia * iw) * ₁₊ w ≡ ia
  p2x = Eq.trans (*-assoc ia iw (₁₊ w))
        (Eq.trans (Eq.cong (ia *_)
                    (lemma-⁻¹ˡ (₁₊ w) {{nztoℕ {y = ₁₊ w} {neq0 = λ ()}}}))
                  (*-identityʳ ia))

  key : x * iw + ia ≡ (ia * iw) * ₁₊ g
  key = Eq.sym (Eq.trans (Eq.cong ((ia * iw) *_) (Eq.sym awb))
        (Eq.trans (*-distribˡ-+ (ia * iw) (x * ₁₊ a₀) (₁₊ w))
                  (Eq.cong₂ _+_ p1x p2x)))

-- An H escape power whose product is - x·a² is - x⁻¹·(a⁻¹)².
KabV : ∀ (x* : ℤ* ₚ) (α' u₁ u₂ : Fin (₁₊ p-2)) →
  ₁₊ u₁ * ₁₊ u₂ ≡ - (x* .proj₁ * (₁₊ α' * ₁₊ α')) →
  Kab u₁ u₂ ≡
    - ((x* ⁻¹) .proj₁ *
       (((₁₊ α' , λ ()) ⁻¹) .proj₁ * ((₁₊ α' , λ ()) ⁻¹) .proj₁))
KabV x* α' u₁ u₂ val = Eq.trans
  (inv-cong ((₁₊ u₁ , λ ()) *' (₁₊ u₂ , λ ()))
            (-' (x* *' ((₁₊ α' , λ ()) *' (₁₊ α' , λ ())))) val)
  (Eq.trans (inv-neg-comm (x* *' ((₁₊ α' , λ ()) *' (₁₊ α' , λ ()))))
    (Eq.cong -_
      (Eq.trans (inv-distrib x* ((₁₊ α' , λ ()) *' (₁₊ α' , λ ())))
        (Eq.cong ((x* ⁻¹) .proj₁ *_)
          (inv-distrib (₁₊ α' , λ ()) (₁₊ α' , λ ()))))))

-- S-power orbit, a = 0 case: the A box is fixed (including its proof)
-- and the E box accumulates - b⁻² at each step.
ract1-S^-a0 : ∀ (k : ℕ) (e : E) (b' : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b') ≢ (₀ , ₀)) →
  ((ract {0} ᵗ) (mk e (₀ , ₁₊ b') nz) (S ^ k)) .proj₂
  ≡ mk (e + nsum k (- (kS-a0 b' nz))) (₀ , ₁₊ b') nz
ract1-S^-a0 zero e b' nz = c1-eq (Eq.sym (+-identityʳ e)) Eq.refl
ract1-S^-a0 (suc zero) e b' nz =
  c1-eq (Eq.cong (e +_) (Eq.sym (+-identityʳ (- (kS-a0 b' nz))))) Eq.refl
ract1-S^-a0 (suc (suc k)) e b' nz =
  Eq.trans (ract1-S^-a0 (suc k) (e + - (kS-a0 b' nz)) b' nz)
           (c1-eq (+-assoc e (- (kS-a0 b' nz)) (nsum (suc k) (- (kS-a0 b' nz)))) Eq.refl)

-- S-power orbit, a ≠ 0 case: the E box is fixed (the escape power is ₀)
-- and the A box accumulates - a in its b component at each step.
ract1-S^-a+ : ∀ (k : ℕ) (e : E) (a' : Fin (₁₊ p-2)) (b : ℤ ₚ)
  (nz : (₁₊ a' , b) ≢ (₀ , ₀)) →
  ((ract {0} ᵗ) (mk e (₁₊ a' , b) nz) (S ^ k)) .proj₂
  ≡ mk e (₁₊ a' , b + nsum k (- (₁₊ a'))) (λ ())
-- The stepping clauses split b: the A-box case tree matches the b
-- component before the gate, so the action is stuck on an abstract b.
ract1-S^-a+ zero e a' b nz =
  c1-eq Eq.refl (Eq.cong (λ z → ₁₊ a' , z) (Eq.sym (+-identityʳ b)))
ract1-S^-a+ (suc zero) e a' b@₀ nz =
  c1-eq (e+-0 e)
        (Eq.cong (λ z → ₁₊ a' , z) (Eq.cong (b +_) (Eq.sym (+-identityʳ (- (₁₊ a'))))))
ract1-S^-a+ (suc zero) e a' b@(₁₊ _) nz =
  c1-eq (e+-0 e)
        (Eq.cong (λ z → ₁₊ a' , z) (Eq.cong (b +_) (Eq.sym (+-identityʳ (- (₁₊ a'))))))
ract1-S^-a+ (suc (suc k)) e a' b@₀ nz =
  Eq.trans (ract1-S^-a+ (suc k) (e + - ₀) a' (b + - (₁₊ a')) (λ ()))
           (c1-eq (e+-0 e)
                  (Eq.cong (λ z → ₁₊ a' , z)
                           (+-assoc b (- (₁₊ a')) (nsum (suc k) (- (₁₊ a'))))))
ract1-S^-a+ (suc (suc k)) e a' b@(₁₊ _) nz =
  Eq.trans (ract1-S^-a+ (suc k) (e + - ₀) a' (b + - (₁₊ a')) (λ ()))
           (c1-eq (e+-0 e)
                  (Eq.cong (λ z → ₁₊ a' , z)
                           (+-assoc b (- (₁₊ a')) (nsum (suc k) (- (₁₊ a'))))))

suc≢0 : ∀ {g : Fin (₁₊ p-2)} → ₁₊ g ≢ ₀
suc≢0 ()

-- Lift a propositional equality of circuits to ≈, width-generically.
refl'ᵣ : ∀ {j} {w v : Circuit j} → w ≡ v → PB._≈_ (j QRel,_===_) w v
refl'ᵣ Eq.refl = PB.refl

-- Rearrange two subtractions.
sub-swap : ∀ (x y z : ℤ ₚ) → (x + - y) + - z ≡ (x + - z) + - y
sub-swap x y z =
  Eq.trans (+-assoc x (- y) (- z))
  (Eq.trans (Eq.cong (x +_) (+-comm (- y) (- z)))
            (Eq.sym (+-assoc x (- z) (- y))))
