------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's affine circuit sends 0 to p and e₀ to q
--
-- α p q = xs p • L (p ⊕ q) (Affine.Alpha).  Its letters toggle bits:
-- X on the wires ι i where p i is set, and the fan-out CX from wire 0,
-- which toggle the bits of the fan exactly when the bit 0 is set.  Read
-- through `togs`, the toggles at the image of an injective map
-- (`lookup-togs`: the bit at ι i flips by p i, the others stay), the
-- fan-out keeps 0 and sends e₀ to w (`L-0`, `L-e`, the latter for w ≠ 0),
-- and the translations add p — so α p q sends 0 to p (`α-0`) and, for
-- p ≠ q, e₀ to q (`α-e`).  With Stable.DecSem.d-sem: the decoding of a
-- gadget on p, q denotes its block on p and q.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Stable.AlphaEnds (n : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using () renaming (suc-injective to sF-inj)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (suc)
open import Data.Product using (Σ ; _,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; replicate)
open import Data.Vec.Properties using (lookup-replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

import Examples.Groups.Clifford+CS.Affine.Theory n as A
import Examples.Groups.Clifford+CS.Affine.Equivariance n as E
import Examples.Groups.Clifford+CS.Affine.Alpha n as Al

open A using (Lt ; Wire ; toggle ; lookup-toggle ; lookup-toggle′ ; fan)

private
  St : Set
  St = Vec Bool (₁₊ n)

------------------------------------------------------------------------
-- Toggles at the image of an injective map

togs : ∀ {k N} → Vec Bool k → (Fin k → Fin N) → Vec Bool N → Vec Bool N
togs []          ι y = y
togs (true  ∷ p) ι y = toggle (togs p (λ i → ι (sF i)) y) (ι 0F)
togs (false ∷ p) ι y = togs p (λ i → ι (sF i)) y

private
  xor-t : ∀ c → not c ≡ (c xor true)
  xor-t true  = Eq.refl
  xor-t false = Eq.refl

  xor-f : ∀ c → c ≡ (c xor false)
  xor-f true  = Eq.refl
  xor-f false = Eq.refl

  vec-ext : ∀ {N} (x y : Vec Bool N) → (∀ i → lookup x i ≡ lookup y i) → x ≡ y
  vec-ext []      []      h = Eq.refl
  vec-ext (a ∷ x) (b ∷ y) h = Eq.cong₂ _∷_ (h 0F) (vec-ext x y (λ i → h (sF i)))

  s≢0 : ∀ {k} {i : Fin k} → sF i ≢ 0F
  s≢0 ()

lookup-togs-out : ∀ {k N} (p : Vec Bool k) (ι : Fin k → Fin N) (y : Vec Bool N) (j : Fin N) →
                  (∀ i → ι i ≢ j) → lookup (togs p ι y) j ≡ lookup y j
lookup-togs-out []          ι y j out = Eq.refl
lookup-togs-out (true  ∷ p) ι y j out =
  Eq.trans (lookup-toggle′ (togs p (λ i → ι (sF i)) y) (ι 0F) j (λ e → out 0F (Eq.sym e)))
           (lookup-togs-out p (λ i → ι (sF i)) y j (λ i → out (sF i)))
lookup-togs-out (false ∷ p) ι y j out = lookup-togs-out p (λ i → ι (sF i)) y j (λ i → out (sF i))

lookup-togs : ∀ {k N} (p : Vec Bool k) (ι : Fin k → Fin N) → (∀ {i j} → ι i ≡ ι j → i ≡ j) →
              (y : Vec Bool N) (i : Fin k) → lookup (togs p ι y) (ι i) ≡ (lookup y (ι i) xor lookup p i)
lookup-togs (true ∷ p) ι inj y 0F =
  Eq.trans (lookup-toggle (togs p (λ i → ι (sF i)) y) (ι 0F))
    (Eq.trans (Eq.cong not (lookup-togs-out p (λ i → ι (sF i)) y (ι 0F) (λ i e → s≢0 (inj e))))
              (xor-t (lookup y (ι 0F))))
lookup-togs (false ∷ p) ι inj y 0F =
  Eq.trans (lookup-togs-out p (λ i → ι (sF i)) y (ι 0F) (λ i e → s≢0 (inj e))) (xor-f (lookup y (ι 0F)))
lookup-togs (true ∷ p) ι inj y (sF i) =
  Eq.trans (lookup-toggle′ (togs p (λ i → ι (sF i)) y) (ι 0F) (ι (sF i)) (λ e → s≢0 (inj e)))
           (lookup-togs p (λ i → ι (sF i)) (λ e → sF-inj (inj e)) y i)
lookup-togs (false ∷ p) ι inj y (sF i) = lookup-togs p (λ i → ι (sF i)) (λ e → sF-inj (inj e)) y i

------------------------------------------------------------------------
-- The letters as toggles

xs-togs : ∀ {k} (p : Vec Bool k) (ι : Fin k → Wire) (y : St) → Al.amapʷ (Al.xs p ι) y ≡ togs p ι y
xs-togs []          ι y = Eq.refl
xs-togs (true  ∷ p) ι y = Eq.cong (λ w → toggle w (ι 0F)) (xs-togs p (λ i → ι (sF i)) y)
xs-togs (false ∷ p) ι y = xs-togs p (λ i → ι (sF i)) y

fan-togs : ∀ {k} (w : Vec Bool k) {ι : Fin k → Fin n} (y : Vec Bool n) →
           Al.amapʷ (fan w ι) (true ∷ y) ≡ true ∷ togs w ι y
fan-togs []          y = Eq.refl
fan-togs (true  ∷ w) {ι} y = Eq.cong (E.tmap 0F (sF (ι 0F))) (fan-togs w {λ i → ι (sF i)} y)
fan-togs (false ∷ w) {ι} y = fan-togs w {λ i → ι (sF i)} y

fan-0 : ∀ {k} (w : Vec Bool k) {ι : Fin k → Fin n} (y : Vec Bool n) →
        Al.amapʷ (fan w ι) (false ∷ y) ≡ false ∷ y
fan-0 []          y = Eq.refl
fan-0 (true  ∷ w) {ι} y = Eq.cong (E.tmap 0F (sF (ι 0F))) (fan-0 w {λ i → ι (sF i)} y)
fan-0 (false ∷ w) {ι} y = fan-0 w {λ i → ι (sF i)} y

------------------------------------------------------------------------
-- The fan-out

z′ : Vec Bool n
z′ = replicate n false

z e₀ : St
z  = false ∷ z′
e₀ = true ∷ z′

private
  togs-id-z : ∀ (w : Vec Bool n) → togs w (λ i → i) z′ ≡ w
  togs-id-z w = vec-ext _ _ λ j →
    Eq.trans (lookup-togs w (λ i → i) (λ e → e) z′ j)
      (Eq.trans (Eq.cong (_xor lookup w j) (lookup-replicate j false)) Eq.refl)

  L0-z : ∀ (w : Vec Bool n) (mb : Maybe (Fin n)) → E.first w ≡ mb → Al.amapʷ (E.L (false ∷ w)) z ≡ z
  L0-z w nothing  e = Eq.subst (λ t → Al.amapʷ t z ≡ z) (Eq.sym (Eq.cong (λ m → E.L₀ m w) e)) Eq.refl
  L0-z w (just j) e =
    Eq.subst (λ t → Al.amapʷ t z ≡ z) (Eq.sym (E.L-false w e))
      (Eq.trans (Eq.cong (E.tmap (sF j) 0F) (fan-0 w z′))
                (Eq.cong (λ c → if c then toggle z 0F else z) (lookup-replicate j false)))

L-0 : ∀ (w : St) → Al.amapʷ (E.L w) z ≡ z
L-0 (true  ∷ w) = fan-0 w z′
L-0 (false ∷ w) = L0-z w (E.first w) Eq.refl

private
  Le-just : ∀ (w : Vec Bool n) (j : Fin n) → E.first w ≡ just j → Al.amapʷ (E.L (false ∷ w)) e₀ ≡ false ∷ w
  Le-just w j e =
    Eq.subst (λ t → Al.amapʷ t e₀ ≡ false ∷ w) (Eq.sym (E.L-false w e))
      (Eq.trans (Eq.cong (E.tmap (sF j) 0F) (Eq.trans (fan-togs w z′) (Eq.cong (true ∷_) (togs-id-z w))))
                (Eq.cong (λ c → if c then toggle (true ∷ w) 0F else true ∷ w) (E.first-just w e)))

L-e : ∀ (w : St) → E.NZ w → Al.amapʷ (E.L w) e₀ ≡ w
L-e (true  ∷ w) _ = Eq.trans (fan-togs w z′) (Eq.cong (true ∷_) (togs-id-z w))
L-e (false ∷ w) (0F , ())
L-e (false ∷ w) (sF i , b) with E.first-some w i b
... | j , e = Le-just w j e

------------------------------------------------------------------------
-- The affine circuit

private
  togs-id : ∀ (p y : St) (j : Fin (₁₊ n)) → lookup (togs p (λ i → i) y) j ≡ (lookup y j xor lookup p j)
  togs-id p y j = lookup-togs p (λ i → i) (λ e → e) y j

α-0 : ∀ (p q : St) → Al.amapʷ (Al.α p q) z ≡ p
α-0 p q =
  Eq.trans (Eq.cong (Al.amapʷ (Al.xs p (λ i → i))) (L-0 (p Al.⊕ q)))
    (Eq.trans (xs-togs p (λ i → i) z)
      (vec-ext _ _ λ j → Eq.trans (togs-id p z j) (lz j)))
  where
  lz : ∀ j → (lookup z j xor lookup p j) ≡ lookup p j
  lz 0F     = Eq.refl
  lz (sF j) = Eq.cong (_xor lookup p (sF j)) (lookup-replicate j false)

α-e : ∀ (p q : St) → p ≢ q → Al.amapʷ (Al.α p q) e₀ ≡ q
α-e p q ne =
  Eq.trans (Eq.cong (Al.amapʷ (Al.xs p (λ i → i))) (L-e (p Al.⊕ q) (Al.nz-⊕ p q ne)))
    (Eq.trans (xs-togs p (λ i → i) (p Al.⊕ q))
      (vec-ext _ _ λ j → Eq.trans (togs-id p (p Al.⊕ q) j)
                           (Eq.trans (Eq.cong (_xor lookup p j) (Al.lookup-⊕ p q j)) (cancel (lookup p j) (lookup q j)))))
  where
  cancel : ∀ a b → ((a xor b) xor a) ≡ b
  cancel true  true  = Eq.refl
  cancel true  false = Eq.refl
  cancel false true  = Eq.refl
  cancel false false = Eq.refl
