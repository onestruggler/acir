------------------------------------------------------------------------
-- Presentations of groups
--
-- The cascade order-p theorem for mb-S, M-column half: iterating the
-- bottom-wire S-cascade's M-column update (PushMbS.mb-S) p times is the
-- identity.
--
-- Method.  Write m ⊞ δ for shifting every D-box b-component and the E
-- box of an M column by constants δ.  The cascade's M-update Φ = mbSm
-- is (i) a-component preserving and (ii) ⊞-equivariant: Φ (m ⊞ δ) =
-- Φ m ⊞ δ.  Any such map satisfies Φ m = m ⊞ σ m with a step σ that is
-- invariant along the ⊞-orbit, so Φ ^ t shifts by t · σ and Φ ^ p by
-- p · σ = 0 (nsum-p≡0) — the abstract module OrderP.
--
-- (i)/(ii) are proven by structural induction up the engine chain.  The
-- only letters the cascade drives through the M column are bottom S,
-- CZ, and the crossings Ex (inside PushBvcz.Wof, via PushMW.push-MW):
--   * S / CZ update boxes by b-translations whose coefficients depend
--     only on the a-components (BR.Two.D.d'-of, DS.d-of-DS,
--     DD-CZ-n.gen-vd'-of), and shift E by a-dependent constants;
--   * the Ex crossing is NOT a translation letterwise (its H letters
--     rotate boxes), but composes to a clean SWAP of the two head
--     D-boxes (dvm-Ex), which conjugates the recursive update one wire
--     up and disappears from the composite (mwM-step).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; zipWith)
open import Data.Vec.Properties using (∷-injective)
open import Data.Fin using (Fin ; toℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base using (Word ; _•_ ; ε ; [_]ʷ ; _^_)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (nsum ; nsum-p≡0)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBword
  p-2 p-prime using (No-Top ; NoTopGen ; sg ; εⁿ ; _•ⁿ_)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMbS
  p-2 p-prime using (mb-S ; mbSⁿ ; Rof ; Rof-nt)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMBword
  p-2 p-prime using (push-MBvec-word)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMW
  p-2 p-prime using (push-MW ; push-lift-M)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBvcz
  p-2 p-prime using (dir-k)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (dvec-word)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ-n
  p-2 p-prime using (gen-vd'-of)

------------------------------------------------------------------------
-- Iteration.

itf : ∀ {X : Set} → (X → X) → ℕ → X → X
itf f zero    x = x
itf f (suc t) x = itf f t (f x)

------------------------------------------------------------------------
-- Arithmetic helpers.

-- (x + y) + z ≡ (x + z) + y.
+-swap : ∀ (x y z : ℤ ₚ) → (x + y) + z ≡ (x + z) + y
+-swap x y z = Eq.trans (+-assoc x y z)
  (Eq.trans (Eq.cong (x +_) (+-comm y z)) (Eq.sym (+-assoc x z y)))

-- b + (b' − b) ≡ b'.
+-cancel : ∀ (b b' : ℤ ₚ) → b + (b' + - b) ≡ b'
+-cancel b b' = Eq.trans (Eq.cong (b +_) (+-comm b' (- b)))
  (Eq.trans (Eq.sym (+-assoc b (- b) b'))
  (Eq.trans (Eq.cong (_+ b') (+-inverseʳ b)) (+-identityˡ b')))

-- (b' + δ) − (b + δ) ≡ b' − b.
diff-shift : ∀ (b b' δ : ℤ ₚ) → (b' + δ) + - (b + δ) ≡ b' + - b
diff-shift b b' δ =
  Eq.trans (Eq.cong ((b' + δ) +_) (Eq.sym (-‿+-comm b δ)))
  (Eq.trans (Eq.sym (+-assoc (b' + δ) (- b) (- δ)))
  (Eq.trans (Eq.cong (_+ - δ) (+-swap b' δ (- b)))
  (Eq.trans (+-assoc (b' + - b) δ (- δ))
  (Eq.trans (Eq.cong ((b' + - b) +_) (+-inverseʳ δ))
            (+-identityʳ (b' + - b))))))

-- − u + − (v + − u) ≡ − v (the Ex swap's core cancellation).
neg-core : ∀ (u v : ℤ ₚ) → - u + - (v + - u) ≡ - v
neg-core u v =
  Eq.trans (Eq.cong (- u +_) (Eq.sym (-‿+-comm v (- u))))
  (Eq.trans (Eq.cong (λ z → - u + (- v + z)) (-‿involutive u))
  (Eq.trans (Eq.cong (- u +_) (+-comm (- v) u))
  (Eq.trans (Eq.sym (+-assoc (- u) u (- v)))
  (Eq.trans (Eq.cong (_+ - v) (+-inverseˡ u)) (+-identityˡ (- v))))))

------------------------------------------------------------------------
-- Shifts: translate every D-box b-component and the E box.

DΔ : ℕ → Set
DΔ k = Vec (ℤ ₚ) k

MΔ : ℕ → Set
MΔ k = DΔ k × ℤ ₚ

shD : D → ℤ ₚ → D
shD (a , b) δ = a , b + δ

infixl 6 _⊞ᵥ_ _⊞_

_⊞ᵥ_ : ∀ {k} → Vec D k → DΔ k → Vec D k
_⊞ᵥ_ = zipWith shD

_⊞_ : ∀ {k} → M (₁₊ k) → MΔ k → M (₁₊ k)
(dv , e) ⊞ (δv , δe) = dv ⊞ᵥ δv , e + δe

_+Δᵥ_ : ∀ {k} → DΔ k → DΔ k → DΔ k
_+Δᵥ_ = zipWith _+_

_+Δ_ : ∀ {k} → MΔ k → MΔ k → MΔ k
(δv , δe) +Δ (γv , γe) = δv +Δᵥ γv , δe + γe

nΔᵥ : ∀ {k} → ℕ → DΔ k → DΔ k
nΔᵥ t = map (nsum t)

nΔ : ∀ {k} → ℕ → MΔ k → MΔ k
nΔ t (δv , δe) = nΔᵥ t δv , nsum t δe

-- a-components.
avecᵥ : ∀ {k} → Vec D k → Vec (ℤ ₚ) k
avecᵥ = map proj₁

avec : ∀ {k} → M (₁₊ k) → Vec (ℤ ₚ) k
avec (dv , e) = avecᵥ dv

-- b/e-differences.
dbd : D → D → ℤ ₚ
dbd d' d = proj₂ d' + - proj₂ d

bdiffᵥ : ∀ {k} → Vec D k → Vec D k → DΔ k
bdiffᵥ = zipWith dbd

bdiff : ∀ {k} → M (₁₊ k) → M (₁₊ k) → MΔ k
bdiff (dv' , e') (dv , e) = bdiffᵥ dv' dv , e' + - e

------------------------------------------------------------------------
-- Shift algebra.

recoverᵥ : ∀ {k} (dv' dv : Vec D k) → avecᵥ dv' ≡ avecᵥ dv →
  dv' ≡ dv ⊞ᵥ bdiffᵥ dv' dv
recoverᵥ [] [] _ = Eq.refl
recoverᵥ ((a' , b') ∷ dv') ((a , b) ∷ dv) eq =
  Eq.cong₂ _∷_
    (Eq.cong₂ _,_ (proj₁ (∷-injective eq))
                  (Eq.sym (+-cancel b b')))
    (recoverᵥ dv' dv (proj₂ (∷-injective eq)))

recover : ∀ {k} (m' m : M (₁₊ k)) → avec m' ≡ avec m →
  m' ≡ m ⊞ bdiff m' m
recover (dv' , e') (dv , e) eq =
  Eq.cong₂ _,_ (recoverᵥ dv' dv eq) (Eq.sym (+-cancel e e'))

bdiffᵥ-⊞ᵥ : ∀ {k} (dv' dv : Vec D k) (δv : DΔ k) →
  bdiffᵥ (dv' ⊞ᵥ δv) (dv ⊞ᵥ δv) ≡ bdiffᵥ dv' dv
bdiffᵥ-⊞ᵥ [] [] [] = Eq.refl
bdiffᵥ-⊞ᵥ ((a' , b') ∷ dv') ((a , b) ∷ dv) (δ ∷ δv) =
  Eq.cong₂ _∷_ (diff-shift b b' δ) (bdiffᵥ-⊞ᵥ dv' dv δv)

bdiff-⊞ : ∀ {k} (m' m : M (₁₊ k)) (δ : MΔ k) →
  bdiff (m' ⊞ δ) (m ⊞ δ) ≡ bdiff m' m
bdiff-⊞ (dv' , e') (dv , e) (δv , δe) =
  Eq.cong₂ _,_ (bdiffᵥ-⊞ᵥ dv' dv δv) (diff-shift e e' δe)

⊞ᵥ-⊞ᵥ : ∀ {k} (dv : Vec D k) (δv γv : DΔ k) →
  dv ⊞ᵥ δv ⊞ᵥ γv ≡ dv ⊞ᵥ (δv +Δᵥ γv)
⊞ᵥ-⊞ᵥ [] [] [] = Eq.refl
⊞ᵥ-⊞ᵥ ((a , b) ∷ dv) (δ ∷ δv) (γ ∷ γv) =
  Eq.cong₂ _∷_ (Eq.cong (a ,_) (+-assoc b δ γ)) (⊞ᵥ-⊞ᵥ dv δv γv)

⊞-⊞ : ∀ {k} (m : M (₁₊ k)) (δ γ : MΔ k) → m ⊞ δ ⊞ γ ≡ m ⊞ (δ +Δ γ)
⊞-⊞ (dv , e) (δv , δe) (γv , γe) =
  Eq.cong₂ _,_ (⊞ᵥ-⊞ᵥ dv δv γv) (+-assoc e δe γe)

-- δ + t · δ ≡ (suc t) · δ (componentwise definitional for nsum).
+Δᵥ-nsum : ∀ {k} (t : ℕ) (δv : DΔ k) → δv +Δᵥ nΔᵥ t δv ≡ nΔᵥ (suc t) δv
+Δᵥ-nsum t [] = Eq.refl
+Δᵥ-nsum t (δ ∷ δv) = Eq.cong ((δ + nsum t δ) ∷_) (+Δᵥ-nsum t δv)

+Δ-nsum : ∀ {k} (t : ℕ) (δ : MΔ k) → δ +Δ nΔ t δ ≡ nΔ (suc t) δ
+Δ-nsum t (δv , δe) = Eq.cong₂ _,_ (+Δᵥ-nsum t δv) Eq.refl

-- 0-fold and p-fold shifts vanish.
⊞ᵥ-0 : ∀ {k} (dv : Vec D k) (δv : DΔ k) → dv ⊞ᵥ nΔᵥ 0 δv ≡ dv
⊞ᵥ-0 [] [] = Eq.refl
⊞ᵥ-0 ((a , b) ∷ dv) (δ ∷ δv) =
  Eq.cong₂ _∷_ (Eq.cong (a ,_) (+-identityʳ b)) (⊞ᵥ-0 dv δv)

⊞-0 : ∀ {k} (m : M (₁₊ k)) (δ : MΔ k) → m ⊞ nΔ 0 δ ≡ m
⊞-0 (dv , e) (δv , δe) = Eq.cong₂ _,_ (⊞ᵥ-0 dv δv) (+-identityʳ e)

⊞ᵥ-p : ∀ {k} (dv : Vec D k) (δv : DΔ k) → dv ⊞ᵥ nΔᵥ p δv ≡ dv
⊞ᵥ-p [] [] = Eq.refl
⊞ᵥ-p ((a , b) ∷ dv) (δ ∷ δv) =
  Eq.cong₂ _∷_
    (Eq.cong (a ,_)
      (Eq.trans (Eq.cong (b +_) (nsum-p≡0 δ)) (+-identityʳ b)))
    (⊞ᵥ-p dv δv)

⊞-p : ∀ {k} (m : M (₁₊ k)) (δ : MΔ k) → m ⊞ nΔ p δ ≡ m
⊞-p (dv , e) (δv , δe) =
  Eq.cong₂ _,_ (⊞ᵥ-p dv δv)
    (Eq.trans (Eq.cong (e +_) (nsum-p≡0 δe)) (+-identityʳ e))

------------------------------------------------------------------------
-- The abstract order-p engine: an a-preserving, ⊞-equivariant map on M
-- has p-th iterate the identity.

module OrderP {k : ℕ}
  (f : M (₁₊ k) → M (₁₊ k))
  (pres  : ∀ m → avec (f m) ≡ avec m)
  (equiv : ∀ m δ → f (m ⊞ δ) ≡ f m ⊞ δ)
  where

  σ : M (₁₊ k) → MΔ k
  σ m = bdiff (f m) m

  step : ∀ m → f m ≡ m ⊞ σ m
  step m = recover (f m) m (pres m)

  σ-const : ∀ m δ → σ (m ⊞ δ) ≡ σ m
  σ-const m δ =
    Eq.trans (Eq.cong (λ z → bdiff z (m ⊞ δ)) (equiv m δ))
             (bdiff-⊞ (f m) m δ)

  shift : ∀ t m → itf f t m ≡ m ⊞ nΔ t (σ m)
  shift zero    m = Eq.sym (⊞-0 m (σ m))
  shift (suc t) m =
    Eq.trans (shift t (f m))
    (Eq.trans (Eq.cong₂ _⊞_ (step m) (Eq.cong (nΔ t) σfm≡σm))
    (Eq.trans (⊞-⊞ m (σ m) (nΔ t (σ m)))
              (Eq.cong (m ⊞_) (+Δ-nsum t (σ m)))))
    where
    σfm≡σm : σ (f m) ≡ σ m
    σfm≡σm = Eq.trans (Eq.cong σ (step m)) (σ-const m (σ m))

  orderp : ∀ m → itf f p m ≡ m
  orderp m = Eq.trans (shift p m) (⊞-p m (σ m))

------------------------------------------------------------------------
-- M-column projections of the cascade engines.

dvm : ∀ {n} → Word (Gen 2) → Vec D (₂₊ n) → Vec D (₂₊ n)
dvm u vd = proj₁ (proj₂ (dvec-word u vd))

mwM : ∀ {n} → M (₂₊ n) → Vec B n → M (₂₊ n)
mwM mm vb = proj₁ (proj₂ (push-MW mm vb))

mbwM : ∀ {n} (W : Word (Gen 2)) → No-Top W → M (₂₊ n) → Vec B n → M (₂₊ n)
mbwM W nt mm vb = proj₁ (proj₂ (push-MBvec-word W nt mm vb))

mbSm : ∀ {k} → M (₁₊ k) → Vec B k → M (₁₊ k)
mbSm m bv = proj₁ (proj₂ (mb-S m bv))

mbSⁿm : ∀ {k} → ℕ → M (₁₊ k) → Vec B k → M (₁₊ k)
mbSⁿm t m bv = proj₁ (proj₂ (mbSⁿ t m bv))

------------------------------------------------------------------------
-- The Ex crossing on the D-vector is the swap of the two head boxes.

dvm-Ex : ∀ {n} (x y : D) (t : Vec D n) → dvm Ex (x ∷ y ∷ t) ≡ y ∷ x ∷ t
dvm-Ex (a , b) (c , d) t =
  Eq.cong₂ _∷_
    (Eq.cong₂ _,_
      (Eq.trans (neg-core (b + - c) (- c)) (-‿involutive c))
      (Eq.trans (Eq.cong -_ (neg-core a d)) (-‿involutive d)))
    (Eq.cong₂ _∷_
      (Eq.cong₂ _,_
        (Eq.trans (neg-core (d + - a) (- a)) (-‿involutive a))
        (Eq.trans (Eq.cong -_ (neg-core c b)) (-‿involutive b)))
      Eq.refl)

------------------------------------------------------------------------
-- CZ-powers on the D-vector: iterated head-pair coupling.

czV : ∀ {n} → ℕ → Vec D (₂₊ n) → Vec D (₂₊ n)
czV t = itf gen-vd'-of t

dvm-CZ^ : ∀ {n} (t : ℕ) (x y : D) (tl : Vec D n) →
  dvm (CZ ^ t) (x ∷ y ∷ tl) ≡ czV t (x ∷ y ∷ tl)
dvm-CZ^ zero          x y tl = Eq.refl
dvm-CZ^ (suc zero)    x y tl = Eq.refl
dvm-CZ^ (suc (suc t)) (a , b) (c , d) tl =
  dvm-CZ^ (suc t) (a , b + - c) (c , d + - a) tl

czV-equiv : ∀ {n} (t : ℕ) (x y : D) (tl : Vec D n) (δ₀ δ₁ : ℤ ₚ)
  (δt : DΔ n) →
  czV t (shD x δ₀ ∷ shD y δ₁ ∷ (tl ⊞ᵥ δt))
  ≡ czV t (x ∷ y ∷ tl) ⊞ᵥ (δ₀ ∷ δ₁ ∷ δt)
czV-equiv zero    x y tl δ₀ δ₁ δt = Eq.refl
czV-equiv (suc t) (a , b) (c , d) tl δ₀ δ₁ δt =
  Eq.trans
    (Eq.cong₂ (λ z w → czV t ((a , z) ∷ (c , w) ∷ (tl ⊞ᵥ δt)))
      (+-swap b δ₀ (- c)) (+-swap d δ₁ (- a)))
    (czV-equiv t (a , b + - c) (c , d + - a) tl δ₀ δ₁ δt)

czV-avec : ∀ {n} (t : ℕ) (x y : D) (tl : Vec D n) →
  avecᵥ (czV t (x ∷ y ∷ tl)) ≡ avecᵥ (x ∷ y ∷ tl)
czV-avec zero    x y tl = Eq.refl
czV-avec (suc t) (a , b) (c , d) tl =
  czV-avec t (a , b + - c) (c , d + - a) tl

------------------------------------------------------------------------
-- The push-MW recursion, in closed form: the two Ex crossings conjugate
-- the recursive call past the second D-box, then the CZ-power couples
-- the head pair.

mwM-step : ∀ {n} (d₀ d₁ : D) (rest : Vec D n) (e : E) (x : B)
  (v : Vec B n) {h : D} {tl : Vec D n} {e2 : E} →
  mwM (d₀ ∷ rest , e) v ≡ (h ∷ tl , e2) →
  mwM (d₀ ∷ d₁ ∷ rest , e) (x ∷ v)
  ≡ (czV (toℕ (dir-k x)) (h ∷ d₁ ∷ tl) , e2)
mwM-step {n} d₀ d₁ rest e x v {h} {tl} {e2} eqrec =
  Eq.trans (Eq.cong (λ z → pM4 (pM3 (pL2 z))) q1)
  (Eq.trans (Eq.cong (λ z → pM4 (pM3 z)) q2)
  (Eq.trans (Eq.cong pM4 q3) q4))
  where
  pL2 : M (₃₊ n) → M (₃₊ n)
  pL2 z = proj₁ (proj₂ (push-lift-M z v))
  pM3 : M (₃₊ n) → M (₃₊ n)
  pM3 z = dvm Ex (proj₁ z) , proj₂ z
  pM4 : M (₃₊ n) → M (₃₊ n)
  pM4 z = dvm (CZ^ (dir-k x)) (proj₁ z) , proj₂ z
  q1 : _≡_ {A = M (₃₊ n)} (dvm Ex (d₀ ∷ d₁ ∷ rest) , e) (d₁ ∷ d₀ ∷ rest , e)
  q1 = Eq.cong (_, e) (dvm-Ex d₀ d₁ rest)
  q2 : pL2 (d₁ ∷ d₀ ∷ rest , e) ≡ (d₁ ∷ h ∷ tl , e2)
  q2 = Eq.cong (λ z → (d₁ ∷ proj₁ z , proj₂ z)) eqrec
  q3 : pM3 (d₁ ∷ h ∷ tl , e2) ≡ (h ∷ d₁ ∷ tl , e2)
  q3 = Eq.cong (_, e2) (dvm-Ex d₁ h tl)
  q4 : pM4 (h ∷ d₁ ∷ tl , e2) ≡ (czV (toℕ (dir-k x)) (h ∷ d₁ ∷ tl) , e2)
  q4 = Eq.cong (_, e2) (dvm-CZ^ (toℕ (dir-k x)) h d₁ tl)

------------------------------------------------------------------------
-- Width-2 base closed forms.  dir-of's case tree splits the D-box's
-- SECOND component (its H clauses force it), so the emitted-exponent
-- projection is stuck on non-constructor b's; these lemmas do the
-- b-split once, then downstream algebra works with general b.

eCZ : ℤ ₚ → ℤ ₚ
eCZ ₀        = ₀
eCZ (₁₊ i)   = ₁₊ i

mwM0 : ∀ (a b : ℤ ₚ) (e : E) →
  mwM ((a , b) ∷ [] , e) [] ≡ ((a , b + - ₁) ∷ [] , e + - eCZ a)
mwM0 ₀      ₀      e = Eq.refl
mwM0 ₀      (₁₊ _) e = Eq.refl
mwM0 (₁₊ i) ₀      e = Eq.refl
mwM0 (₁₊ i) (₁₊ _) e = Eq.refl

mbwS0 : ∀ (pr : NoTopGen (gate₁ S-gate)) (a b : ℤ ₚ) (e : E)
  (vb : Vec B 0) →
  mbwM [ gate₁ S-gate ]ʷ (sg pr) ((a , b) ∷ [] , e) vb
  ≡ ((a , b + - a) ∷ [] , e + - ₀)
mbwS0 pr ₀      ₀      e vb = Eq.refl
mbwS0 pr ₀      (₁₊ _) e vb = Eq.refl
mbwS0 pr (₁₊ _) ₀      e vb = Eq.refl
mbwS0 pr (₁₊ _) (₁₊ _) e vb = Eq.refl

------------------------------------------------------------------------
-- push-MW: a-preservation and ⊞-equivariance.

-- Destructuring view: every M (₂₊ n) is a cons plus an E box.  Using
-- this in a `let` (instead of `with … in`) avoids the with-machinery's
-- goal normalization — normalizing an mwM application explodes (the Ex
-- crossing's ring terms nest exponentially).
mView : ∀ {n} (z : M (₂₊ n)) →
  ∃ λ h → ∃ λ tl → ∃ λ e2 → z ≡ (h ∷ tl , e2)
mView (h ∷ tl , e2) = h , tl , e2 , Eq.refl

mwM-avec : ∀ {n} (mm : M (₂₊ n)) (vb : Vec B n) →
  avec (mwM mm vb) ≡ avec mm
mwM-avec {zero} ((a , b) ∷ [] , e) [] = Eq.cong avec (mwM0 a b e)
mwM-avec {suc n} (d₀ ∷ d₁ ∷ rest , e) (x ∷ v) =
  let (h , tl , e2 , eqrec) = mView (mwM (d₀ ∷ rest , e) v)
      ihEq = Eq.trans (Eq.cong avec (Eq.sym eqrec))
                      (mwM-avec (d₀ ∷ rest , e) v)
  in
  Eq.trans (Eq.cong avec (mwM-step d₀ d₁ rest e x v eqrec))
  (Eq.trans (czV-avec (toℕ (dir-k x)) h d₁ tl)
    (Eq.cong₂ _∷_ (proj₁ (∷-injective ihEq))
      (Eq.cong (proj₁ d₁ ∷_) (proj₂ (∷-injective ihEq)))))

mwM-equiv : ∀ {n} (mm : M (₂₊ n)) (vb : Vec B n) (δ : MΔ (₁₊ n)) →
  mwM (mm ⊞ δ) vb ≡ mwM mm vb ⊞ δ
mwM-equiv {zero} ((a , b) ∷ [] , e) [] (δ₀ ∷ [] , δe) =
  Eq.trans (mwM0 a (b + δ₀) (e + δe))
  (Eq.trans
    (Eq.cong₂ _,_
      (Eq.cong (λ z → (a , z) ∷ []) (+-swap b δ₀ (- ₁)))
      (+-swap e δe (- eCZ a)))
    (Eq.sym (Eq.cong (_⊞ (δ₀ ∷ [] , δe)) (mwM0 a b e))))
mwM-equiv {suc n} (d₀ ∷ d₁ ∷ rest , e) (x ∷ v) ((δ₀ ∷ δ₁ ∷ δr) , δe) =
  let (h , tl , e2 , eqrec) = mView (mwM (d₀ ∷ rest , e) v)
      eqShift = Eq.trans (mwM-equiv (d₀ ∷ rest , e) v ((δ₀ ∷ δr) , δe))
                         (Eq.cong (_⊞ ((δ₀ ∷ δr) , δe)) eqrec)
  in
  Eq.trans
    (mwM-step (shD d₀ δ₀) (shD d₁ δ₁) (rest ⊞ᵥ δr) (e + δe) x v eqShift)
  (Eq.trans
    (Eq.cong (_, e2 + δe) (czV-equiv (toℕ (dir-k x)) h d₁ tl δ₀ δ₁ δr))
    (Eq.sym (Eq.cong (_⊞ ((δ₀ ∷ δ₁ ∷ δr) , δe))
      (mwM-step d₀ d₁ rest e x v eqrec))))

------------------------------------------------------------------------
-- S/CZ-only words: the vocabulary the cascade actually drives through
-- push-MBvec-word (the letters of Rof are bottom S and CZ powers).

data SC : Word (Gen 2) → Set where
  sc-S  : SC ([ gate₁ S-gate ]ʷ)
  sc-CZ : SC ([ gate₂ CZ-gate ]ʷ)
  sc-ε  : SC ε
  _•ˢᶜ_ : ∀ {u v} → SC u → SC v → SC (u • v)

sc-^ : ∀ {w} → SC w → (t : ℕ) → SC (w ^ t)
sc-^ sw zero          = sc-ε
sc-^ sw (suc zero)    = sw
sc-^ sw (suc (suc t)) = sw •ˢᶜ sc-^ sw (suc t)

sc-Rof : (b : B) → SC (Rof b)
sc-Rof (₀ , ₀)          = sc-ε
sc-Rof (₀ , b@(₁₊ _))   =
  sc-^ sc-S (toℕ (b * b)) •ˢᶜ sc-^ sc-CZ (toℕ (- b))
sc-Rof (a@(₁₊ _) , b)   =
  sc-^ sc-S (toℕ (a * a)) •ˢᶜ sc-^ sc-CZ (toℕ (- a))

------------------------------------------------------------------------
-- push-MBvec-word on S/CZ-only words: a-preservation and equivariance.

mbw-avec : ∀ {n} (W : Word (Gen 2)) (nt : No-Top W) → SC W →
  (mm : M (₂₊ n)) (vb : Vec B n) → avec (mbwM W nt mm vb) ≡ avec mm
mbw-avec ε εⁿ sc-ε mm vb = Eq.refl
mbw-avec [ gate₁ H-gate ]ʷ nt () mm vb
mbw-avec [ g ↥ ]ʷ nt () mm vb
mbw-avec {zero} [ gate₁ S-gate ]ʷ (sg pr) sc-S ((a , b) ∷ [] , e) vb =
  Eq.cong avec (mbwS0 pr a b e vb)
mbw-avec {suc n} [ gate₁ S-gate ]ʷ (sg pr) sc-S ((₀ , b) ∷ h ∷ t , e) vb =
  Eq.refl
mbw-avec {suc n} [ gate₁ S-gate ]ʷ (sg pr) sc-S ((₁₊ i , b) ∷ h ∷ t , e) vb =
  Eq.refl
mbw-avec [ gate₂ CZ-gate ]ʷ nt sc-CZ mm vb = mwM-avec mm vb
mbw-avec (u • v) (ntu •ⁿ ntv) (scu •ˢᶜ scv) mm vb =
  Eq.trans (mbw-avec v ntv scv (mbwM u ntu mm vb) vb)
           (mbw-avec u ntu scu mm vb)

mbw-equiv : ∀ {n} (W : Word (Gen 2)) (nt : No-Top W) → SC W →
  (mm : M (₂₊ n)) (vb : Vec B n) (δ : MΔ (₁₊ n)) →
  mbwM W nt (mm ⊞ δ) vb ≡ mbwM W nt mm vb ⊞ δ
mbw-equiv ε εⁿ sc-ε mm vb δ = Eq.refl
mbw-equiv [ gate₁ H-gate ]ʷ nt () mm vb δ
mbw-equiv [ g ↥ ]ʷ nt () mm vb δ
mbw-equiv {zero} [ gate₁ S-gate ]ʷ (sg pr) sc-S ((a , b) ∷ [] , e) vb
  (δ₀ ∷ [] , δe) =
  Eq.trans (mbwS0 pr a (b + δ₀) (e + δe) vb)
  (Eq.trans
    (Eq.cong₂ _,_
      (Eq.cong (λ z → (a , z) ∷ []) (+-swap b δ₀ (- a)))
      (+-swap e δe (- ₀)))
    (Eq.sym (Eq.cong (_⊞ (δ₀ ∷ [] , δe)) (mbwS0 pr a b e vb))))
mbw-equiv {suc n} [ gate₁ S-gate ]ʷ (sg pr) sc-S ((₀ , b) ∷ h ∷ t , e) vb
  ((δ₀ ∷ δh ∷ δt) , δe) = Eq.refl
mbw-equiv {suc n} [ gate₁ S-gate ]ʷ (sg pr) sc-S ((₁₊ i , b) ∷ h ∷ t , e) vb
  ((δ₀ ∷ δh ∷ δt) , δe) =
  Eq.cong (λ z → ((₁₊ i , z) ∷ shD h δh ∷ (t ⊞ᵥ δt) , e + δe))
    (+-swap b δ₀ (- ₁₊ i))
mbw-equiv [ gate₂ CZ-gate ]ʷ nt sc-CZ mm vb δ = mwM-equiv mm vb δ
mbw-equiv (u • v) (ntu •ⁿ ntv) (scu •ˢᶜ scv) mm vb δ =
  Eq.trans (Eq.cong (λ z → mbwM v ntv z vb) (mbw-equiv u ntu scu mm vb δ))
           (mbw-equiv v ntv scv (mbwM u ntu mm vb) vb δ)

------------------------------------------------------------------------
-- mb-S: a-preservation and ⊞-equivariance.

mbS-avec : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) → avec (mbSm m bv) ≡ avec m
mbS-avec {zero} ([] , e) [] = Eq.refl
mbS-avec {suc k'} (d₀ ∷ dr , e) (b₀ ∷ bv') =
  Eq.trans
    (mbw-avec (Rof b₀) (Rof-nt b₀) (sc-Rof b₀)
      (d₀ ∷ proj₁ (mbSm (dr , e) bv') , proj₂ (mbSm (dr , e) bv')) bv')
    (Eq.cong (proj₁ d₀ ∷_) (mbS-avec (dr , e) bv'))

mbS-equiv : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) (δ : MΔ k) →
  mbSm (m ⊞ δ) bv ≡ mbSm m bv ⊞ δ
mbS-equiv {zero} ([] , e) [] ([] , δe) =
  Eq.cong ([] ,_) (+-swap e δe (- ₁))
mbS-equiv {suc k'} (d₀ ∷ dr , e) (b₀ ∷ bv') ((δ₀ ∷ δr) , δe) =
  Eq.trans
    (Eq.cong
      (λ z → mbwM (Rof b₀) (Rof-nt b₀) (shD d₀ δ₀ ∷ proj₁ z , proj₂ z) bv')
      (mbS-equiv (dr , e) bv' (δr , δe)))
    (mbw-equiv (Rof b₀) (Rof-nt b₀) (sc-Rof b₀)
      (d₀ ∷ proj₁ (mbSm (dr , e) bv') , proj₂ (mbSm (dr , e) bv')) bv'
      ((δ₀ ∷ δr) , δe))

------------------------------------------------------------------------
-- mbSⁿ: one S peels off the front; a-preservation and equivariance.

mbSⁿ-step : ∀ {k} (t : ℕ) (m : M (₁₊ k)) (bv : Vec B k) →
  mbSⁿm (suc t) m bv ≡ mbSⁿm t (mbSm m bv) bv
mbSⁿ-step zero    m bv = Eq.refl
mbSⁿ-step (suc t) m bv = Eq.refl

mbSⁿ-avec : ∀ {k} (t : ℕ) (m : M (₁₊ k)) (bv : Vec B k) →
  avec (mbSⁿm t m bv) ≡ avec m
mbSⁿ-avec zero    m bv = Eq.refl
mbSⁿ-avec (suc t) m bv =
  Eq.trans (Eq.cong avec (mbSⁿ-step t m bv))
  (Eq.trans (mbSⁿ-avec t (mbSm m bv) bv) (mbS-avec m bv))

mbSⁿ-equiv : ∀ {k} (t : ℕ) (m : M (₁₊ k)) (bv : Vec B k) (δ : MΔ k) →
  mbSⁿm t (m ⊞ δ) bv ≡ mbSⁿm t m bv ⊞ δ
mbSⁿ-equiv zero    m bv δ = Eq.refl
mbSⁿ-equiv (suc t) m bv δ =
  Eq.trans (mbSⁿ-step t (m ⊞ δ) bv)
  (Eq.trans (Eq.cong (λ z → mbSⁿm t z bv) (mbS-equiv m bv δ))
  (Eq.trans (mbSⁿ-equiv t (mbSm m bv) bv δ)
            (Eq.cong (_⊞ δ) (Eq.sym (mbSⁿ-step t m bv)))))

------------------------------------------------------------------------
-- The order-p theorems.

mbS-orderp : ∀ {k} (bv : Vec B k) (m : M (₁₊ k)) →
  itf (λ z → mbSm z bv) p m ≡ m
mbS-orderp bv = OP.orderp
  where
  module OP = OrderP (λ z → mbSm z bv)
    (λ m → mbS-avec m bv) (λ m δ → mbS-equiv m bv δ)

mbSⁿ-orderp : ∀ {k} (t : ℕ) (bv : Vec B k) (m : M (₁₊ k)) →
  itf (λ z → mbSⁿm t z bv) p m ≡ m
mbSⁿ-orderp t bv = OP.orderp
  where
  module OP = OrderP (λ z → mbSⁿm t z bv)
    (λ m → mbSⁿ-avec t m bv) (λ m δ → mbSⁿ-equiv t m bv δ)
