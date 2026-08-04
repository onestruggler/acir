------------------------------------------------------------------------
-- Presentations of groups
--
-- The keystone commutation for the inj₁ structural cases of the coset
-- action's well-definedness: the bottom-wire S-cascade (mb-S / mbSⁿ) and
-- the top-gate push (mbv-push) commute on an M-column · B-vector.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.Keystone
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Vec using (Vec ; [] ; _∷_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMbS p-2 p-prime
  using (mb-S ; mbSⁿ)
import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as DW
import Examples.Groups.Symplectic.BR.Two.D p-2 p-prime as TD
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (dvec-word)
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (d-of-DS)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ-n p-2 p-prime
  using (gen-vd'-of)
open import Data.Nat using (zero ; suc)

private variable
  k : ℕ

------------------------------------------------------------------------
-- Projections of the two pushes onto the M-column / B-vector.

-- mb-S leaves the B-vector fixed; its M-column output:
mbSm : (m : M (₁₊ k)) (bv : Vec B k) → M (₁₊ k)
mbSm m bv = proj₁ (proj₂ (mb-S m bv))

-- mbSⁿ (S ^ j) M-column output:
mbSⁿm : (j : ℕ) (m : M (₁₊ k)) (bv : Vec B k) → M (₁₊ k)
mbSⁿm j m bv = proj₁ (proj₂ (mbSⁿ j m bv))

-- mbv-push M-column / B-vector outputs:
mbv-M : (m : M (₁₊ k)) (bv : Vec B k) (g : Gen k) → M (₁₊ k)
mbv-M m bv g = proj₁ (proj₂ (ML'T.mbv-push m bv g))

mbv-B : (m : M (₁₊ k)) (bv : Vec B k) (g : Gen k) → Vec B k
mbv-B m bv g = proj₂ (proj₂ (ML'T.mbv-push m bv g))

------------------------------------------------------------------------
-- The B-vector output of mbv-push does not depend on the M-column.
--
-- mbv-push reads the B-vector and the gate to update the B-vector; the
-- M-column (D-vector · E) is never consulted for the B-output.

mbv-B-indep : ∀ {k} (m m' : M (₁₊ k)) (bv : Vec B k) (g : Gen k) →
  proj₂ (proj₂ (ML'T.mbv-push m bv g)) ≡ proj₂ (proj₂ (ML'T.mbv-push m' bv g))
mbv-B-indep m m' bv (gate₂ CZ-gate) = Eq.refl
mbv-B-indep (d₁ ∷ dr' , e) (d₁' ∷ dr'' , e') (b₁ ∷ bv') (gate₁ y) = Eq.refl
mbv-B-indep (d₁ ∷ dr' , e) (d₁' ∷ dr'' , e') (b₁ ∷ bv') (h ↥) =
  Eq.cong (b₁ ∷_) (mbv-B-indep (dr' , e) (dr'' , e') bv' h)

------------------------------------------------------------------------
-- Closed forms for push-D-w over the atomic S-power / CZ-power words.
--
-- push-D-w threads the affine D-box maps letter-by-letter (D.d'-of):
--   S : (a,b) ↦ (a, b-a)      CZ : (a,b) ↦ (a, b-1).

it : ∀ {A : Set} → (A → A) → ℕ → A → A
it f zero    x = x
it f (suc n) x = it f n (f x)

dS dCZ : D → D
dS  (a , b) = a , b + - a
dCZ (a , b) = a , b + - ₁

pdw-Sⁿ : ∀ (n : ℕ) (d : D) →
  proj₂ (proj₂ (DW.push-D-w d (S ^ n) (DW.ntH-^ DW.ntH-S n))) ≡ it dS n d
pdw-Sⁿ zero          d = Eq.refl
pdw-Sⁿ (suc zero)    d = Eq.refl
pdw-Sⁿ (suc (suc m)) d = pdw-Sⁿ (suc m) (dS d)

pdw-CZⁿ : ∀ (n : ℕ) (d : D) →
  proj₂ (proj₂ (DW.push-D-w d (CZ ^ n) (DW.ntH-^ DW.ntH-CZ n))) ≡ it dCZ n d
pdw-CZⁿ zero          d = Eq.refl
pdw-CZⁿ (suc zero)    d = Eq.refl
pdw-CZⁿ (suc (suc m)) d = pdw-CZⁿ (suc m) (dCZ d)

------------------------------------------------------------------------
-- Algebraic commutation helpers for the affine D-box maps.

-- Commuting endos iterate-commute: it f m ∘ it g n ≡ it g n ∘ it f m.
it-swap : ∀ {X : Set} (f g : X → X) → (∀ x → f (g x) ≡ g (f x)) →
  ∀ (m n : ℕ) (x : X) → it f m (it g n x) ≡ it g n (it f m x)
it-swap {X} f g comm zero    n x = Eq.refl
it-swap {X} f g comm (suc m) n x =
  Eq.trans (Eq.cong (it f m) (push x n)) (it-swap f g comm m n (f x))
  where
  -- one f commutes past a block of g's
  push : ∀ (x : X) (n : ℕ) → f (it g n x) ≡ it g n (f x)
  push x zero    = Eq.refl
  push x (suc n) = Eq.trans (push (g x) n) (Eq.cong (it g n) (comm x))

-- dS and dCZ commute: both fix the a-component and translate b.
dS-dCZ : ∀ d → dS (dCZ d) ≡ dCZ (dS d)
dS-dCZ (a , b) = Eq.cong (a ,_)
  (Eq.trans (+-assoc b (- ₁) (- a))
  (Eq.trans (Eq.cong (b +_) (+-comm (- ₁) (- a)))
            (Eq.sym (+-assoc b (- a) (- ₁)))))

-- Rearrange two subtractions: (x - y) - z ≡ (x - z) - y.
sub-swap : ∀ (x y z : ℤ ₚ) → (x + - y) + - z ≡ (x + - z) + - y
sub-swap x y z =
  Eq.trans (+-assoc x (- y) (- z))
  (Eq.trans (Eq.cong (x +_) (+-comm (- y) (- z)))
            (Eq.sym (+-assoc x (- z) (- y))))

-- Apply a D-endo to the head of a D-vector.
onhead : ∀ {N} → (D → D) → Vec D (₂₊ N) → Vec D (₂₊ N)
onhead f (d ∷ rest) = f d ∷ rest

-- The wire-0 S-cascade (onhead d-of-DS) commutes with the wire-0/1 CZ
-- coupling (gen-vd'-of): both touch the head b-component additively.
dDS-genvd : ∀ {N} (vd : Vec D (₂₊ N)) →
  onhead d-of-DS (gen-vd'-of vd) ≡ gen-vd'-of (onhead d-of-DS vd)
dDS-genvd ((₀ , b)        ∷ (c , d) ∷ t) = Eq.refl
dDS-genvd ((a′@(₁₊ a) , b) ∷ (c , d) ∷ t) =
  Eq.cong (λ z → (a′ , z) ∷ (c , d + - a′) ∷ t) (sub-swap b c a′)

------------------------------------------------------------------------
-- Closed form for dvec-word over an S-power: the wire-0 S-cascade updates
-- only the head D-box (via d-of-DS), leaving the rest of the vector fixed.

dvec-Sⁿ : ∀ (n : ℕ) {N} (d₁ h : D) (t : Vec D N) →
  proj₁ (proj₂ (dvec-word (S ^ n) (d₁ ∷ h ∷ t))) ≡ it d-of-DS n d₁ ∷ h ∷ t
dvec-Sⁿ zero          d₁ h t = Eq.refl
dvec-Sⁿ (suc zero)    d₁ h t = Eq.refl
dvec-Sⁿ (suc (suc m)) d₁ h t = dvec-Sⁿ (suc m) (d-of-DS d₁) h t

-- Closed form for dvec-word over a CZ-power: the wire-0/1 CZ-cascade
-- couples only the first two D-boxes (gen-vd'-of), leaving the rest fixed.
dvec-CZⁿ : ∀ (n : ℕ) {N} (d₁ h : D) (t : Vec D N) →
  proj₁ (proj₂ (dvec-word (CZ ^ n) (d₁ ∷ h ∷ t))) ≡ it gen-vd'-of n (d₁ ∷ h ∷ t)
dvec-CZⁿ zero          d₁ h t = Eq.refl
dvec-CZⁿ (suc zero)    d₁ h t = Eq.refl
dvec-CZⁿ (suc (suc m)) (a , b) (c , d) t = dvec-CZⁿ (suc m) (a , b + - c) (c , d + - a) t

------------------------------------------------------------------------
-- Single-S ⋈ single-gate commutation on the M-column (the hard core).
--
-- Pushing g (top) then one S (bottom) equals pushing one S then g, on the
-- M-column.  The B-vector fed to mb-S on the left is the g-updated one
-- (mbv-B); mbv-B-indep bridges it to the original on the right.

core-M1 : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) (g : Gen k) →
  mbSm (mbv-M m bv g) (mbv-B m bv g) ≡ mbv-M (mbSm m bv) bv g
core-M1 m bv (gate₂ CZ-gate) = {!!}
core-M1 (d₁ ∷ dr' , e) (b₁ ∷ bv') (gate₁ y) = {!!}
core-M1 (d₁ ∷ dr' , e) (b₁ ∷ bv') (h ↥) = {!!}

------------------------------------------------------------------------
-- One S peels off the front of S ^ (suc j).

mbSⁿ-step : ∀ {k} (j : ℕ) (m : M (₁₊ k)) (bv : Vec B k) →
  mbSⁿm (suc j) m bv ≡ mbSⁿm j (mbSm m bv) bv
mbSⁿ-step zero    m bv = Eq.refl
mbSⁿ-step (suc j) m bv = Eq.refl

------------------------------------------------------------------------
-- General S ^ j ⋈ gate commutation on the M-column, by induction on j.

core-M : ∀ {k} (j : ℕ) (m : M (₁₊ k)) (bv : Vec B k) (g : Gen k) →
  mbSⁿm j (mbv-M m bv g) (mbv-B m bv g) ≡ mbv-M (mbSⁿm j m bv) bv g
core-M zero    m bv g = Eq.refl
core-M (suc j) m bv g
  rewrite mbSⁿ-step j (mbv-M m bv g) (mbv-B m bv g)
        | mbSⁿ-step j m bv
        | core-M1 m bv g
        | mbv-B-indep m (mbSm m bv) bv g
  = core-M j (mbSm m bv) bv g

------------------------------------------------------------------------
-- The coset half of the keystone: the bottom-gate update (Push.ract, an
-- iterated S-push whose exponent comes from the A box) and the top-gate
-- update (ML'-Top.ml'-of / mbv-push) commute on an ML' box.  The M
-- column commutes by core-M, the B-vector by mbv-B-indep, and the A box
-- (hence the S-power exponent and the A residual) is untouched by the
-- top-gate push.

open import Data.Fin using (toℕ)
import Examples.Groups.Symplectic.Normalization.Pushing.Push p-2 p-prime as Push
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (A-dir-S-power)

ml'-of-comm : ∀ {k} (ml' : ML' (₂₊ k)) (g : Gen (₁₊ k)) (h : SympGate 1) →
  proj₂ (Push.ract (ML'T.ml'-of ml' g) h) ≡ ML'T.ml'-of (proj₂ (Push.ract ml' h)) g
ml'-of-comm {k} ((dv , e) , (bv , a)) g h =
  Eq.cong₂ (λ mm bb → mm , (bb , _))
    (core-M (toℕ j) (dv , e) bv g)
    (mbv-B-indep (dv , e) (mbSⁿm (toℕ j) (dv , e) bv) bv g)
  where
  gk : Gen (₂₊ k)
  gk = gate₁ h
  j : ℤ ₚ
  j = A-dir-S-power a gk (Push.bws1 h) .proj₁
