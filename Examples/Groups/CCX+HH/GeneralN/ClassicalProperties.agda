------------------------------------------------------------------------
-- Presentations of groups
--
-- Inverses and elementary affine gadgets for the adjacent classical
-- compiler.  All equalities are pointwise on every bit assignment.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.ClassicalProperties where

open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH.GeneralN.Classical
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons)

private variable n : ℕ

xor-twice : ∀ a b → (a xor b) xor b ≡ a
xor-twice false false = refl
xor-twice false true = refl
xor-twice true false = refl
xor-twice true true = refl

xor-self : ∀ a → a xor a ≡ false
xor-self false = refl
xor-self true = refl

inverse : Circuit n → Circuit n
inverse [ g ]ʷ = [ g ]ʷ
inverse ε = ε
inverse (u • v) = inverse v • inverse u

act₀-involutive : ∀ (g : Gen n) s → act₀ g (act₀ g s) ≈s s
act₀-involutive (gate₀ ()) s i
act₀-involutive (gate₁ X-gate) s zero = xor-twice (s zero) true
act₀-involutive (gate₁ X-gate) s (suc i) = refl
act₀-involutive (gate₂ CX-gate) s zero = xor-twice (s zero) (s (suc zero))
act₀-involutive (gate₂ CX-gate) s (suc i) = refl
act₀-involutive (gate₂ SWAP-gate) s zero = refl
act₀-involutive (gate₂ SWAP-gate) s (suc zero) = refl
act₀-involutive (gate₂ SWAP-gate) s (suc (suc i)) = refl
act₀-involutive (gate₃ CCX-gate) s zero = xor-twice (s zero) _
act₀-involutive (gate₃ CCX-gate) s (suc i) = refl
act₀-involutive (g ↥) s zero = refl
act₀-involutive (g ↥) s (suc i) = act₀-involutive g (lower s) i

inverse-correct : ∀ (w : Circuit n) s → act (inverse w) (act w s) ≈s s
inverse-correct [ g ]ʷ = act₀-involutive g
inverse-correct ε s i = refl
inverse-correct (u • v) s i = trans
  (act-cong (inverse v) (inverse-correct u (act v s)) i) (inverse-correct v s i)

inverse-involutive : ∀ (w : Circuit n) → inverse (inverse w) ≡ w
inverse-involutive [ g ]ʷ = refl
inverse-involutive ε = refl
inverse-involutive (u • v) = cong₂ _•_ (inverse-involutive u) (inverse-involutive v)

inverse-correctʳ : ∀ (w : Circuit n) s → act w (act (inverse w) s) ≈s s
inverse-correctʳ w s i = trans
  (cong (λ v → act v (act (inverse w) s) i) (sym (inverse-involutive w)))
  (inverse-correct (inverse w) s i)

act-injective : ∀ (w : Circuit n) {s t} → act w s ≈s act w t → s ≈s t
act-injective w {s} {t} eq i = trans (sym (inverse-correct w s i))
  (trans (act-cong (inverse w) eq i) (inverse-correct w t i))

zeros : State n
zeros i = false

e₀ : State (suc n)
e₀ zero = true
e₀ (suc i) = false

e₁ : State (suc (suc n))
e₁ zero = false
e₁ (suc zero) = true
e₁ (suc (suc i)) = false

cons-cong : ∀ {b c} {s t : State n} → b ≡ c → s ≈s t → cons b s ≈s cons c t
cons-cong bc st zero = bc
cons-cong bc st (suc i) = st i

cons-view : ∀ (s : State (suc n)) → cons (s zero) (lower s) ≈s s
cons-view s zero = refl
cons-view s (suc i) = refl

act-up-cons : ∀ (w : Circuit n) b s → act (w ↑) (cons b s) ≈s cons b (act w s)
act-up-cons w b s zero = shift-correct w (cons b s) zero
act-up-cons w b s (suc i) = shift-correct w (cons b s) (suc i)

CX₀₁ : Circuit (suc (suc n))
CX₀₁ = [ gate₂ SWAP-gate ]ʷ • [ gate₂ CX-gate ]ʷ • [ gate₂ SWAP-gate ]ʷ

CX₀₁-head : ∀ (s : State (suc (suc n))) → act CX₀₁ s zero ≡ s zero
CX₀₁-head s = refl

CX₀₁-next : ∀ (s : State (suc (suc n))) → act CX₀₁ s (suc zero) ≡ s (suc zero) xor s zero
CX₀₁-next s = refl

Xbit : Bool → Circuit (suc n)
Xbit false = ε
Xbit true = [ gate₁ X-gate ]ʷ

Xbit-head : ∀ b s → act (Xbit {n} b) s zero ≡ s zero xor b
Xbit-head false s = sym (xor-identityʳ (s zero))
Xbit-head true s = refl

Xbit-tail : ∀ b s i → act (Xbit {n} b) s (suc i) ≡ s (suc i)
Xbit-tail false s i = refl
Xbit-tail true s i = refl

translate : ∀ n → State n → Circuit n
translate zero mask = ε
translate (suc n) mask = Xbit (mask zero) • (translate n (lower mask) ↑)

translate-correct : ∀ n mask s i → act (translate n mask) s i ≡ s i xor mask i
translate-correct zero mask s ()
translate-correct (suc n) mask s zero = trans
  (Xbit-head (mask zero) (act (translate n (lower mask) ↑) s))
  (cong (_xor mask zero) (shift-correct (translate n (lower mask)) s zero))
translate-correct (suc n) mask s (suc i) = trans
  (Xbit-tail (mask zero) (act (translate n (lower mask) ↑) s) i)
  (trans (shift-correct (translate n (lower mask)) s (suc i))
    (translate-correct n (lower mask) (lower s) i))

translate-self : ∀ n s → act (translate n s) s ≈s zeros
translate-self n s i = trans (translate-correct n s s i) (xor-self (s i))
