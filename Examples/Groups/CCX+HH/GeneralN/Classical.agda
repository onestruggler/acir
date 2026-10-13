------------------------------------------------------------------------
-- Presentations of groups
--
-- Adjacent classical gates, their action on arbitrary bit assignments,
-- and their expansion into the physical X,CX,CCX,HH circuit alphabet.
-- SWAP is the actual macro CX HH CX HH CX in the expanded circuit.
-- The Boolean semantics here is independent of that expansion; its
-- comparison with quantum vector semantics is a separate theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.Classical where

open import Data.Bool.Base using (Bool ; _xor_ ; _∧_ ; true)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; cong₂ ; trans)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Circuit.Base
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.GeneralN.BorrowedBit as Borrowed
import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.Semantics as SP
import Examples.Groups.Symmetric.Interpretation as SI
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)

private variable n : ℕ

data Gate : ℕ → Set where
  X-gate : Gate 1
  CX-gate SWAP-gate : Gate 2
  CCX-gate : Gate 3

private module C = Circuit.Base Gate
open C public using
  ( Gen ; Circuit ; gate₀ ; gate₁ ; gate₂ ; gate₃
  ; _↥ ; _↑ ; _↧ ; _⇓ )

State : ℕ → Set
State n = Fin n → Bool

infix 4 _≈s_
_≈s_ : State n → State n → Set
s ≈s t = ∀ i → s i ≡ t i

lower : State (suc n) → State n
lower s i = s (suc i)

shift : (State n → State n) → State (suc n) → State (suc n)
shift f s zero = s zero
shift f s (suc i) = f (lower s) i

x : State (suc n) → State (suc n)
x s zero = s zero xor true
x s (suc i) = s (suc i)

cx : State (suc (suc n)) → State (suc (suc n))
cx s zero = s zero xor s (suc zero)
cx s (suc i) = s (suc i)

ccx : State (suc (suc (suc n))) → State (suc (suc (suc n)))
ccx s zero = s zero xor (s (suc zero) ∧ s (suc (suc zero)))
ccx s (suc i) = s (suc i)

swap : State (suc (suc n)) → State (suc (suc n))
swap s zero = s (suc zero)
swap s (suc zero) = s zero
swap s (suc (suc i)) = s (suc (suc i))

act₀ : Gen n → State n → State n
act₀ (gate₀ ())
act₀ (gate₁ X-gate) = x
act₀ (gate₂ CX-gate) = cx
act₀ (gate₂ SWAP-gate) = swap
act₀ (gate₃ CCX-gate) = ccx
act₀ (g ↥) = shift (act₀ g)

act : Circuit n → State n → State n
act [ g ]ʷ = act₀ g
act ε s = s
act (u • v) s = act u (act v s)

act₀-cong : ∀ (g : Gen n) {s t} → s ≈s t → act₀ g s ≈s act₀ g t
act₀-cong (gate₀ ()) eq i
act₀-cong (gate₁ X-gate) eq zero = cong (_xor true) (eq zero)
act₀-cong (gate₁ X-gate) eq (suc i) = eq (suc i)
act₀-cong (gate₂ CX-gate) eq zero = cong₂ _xor_ (eq zero) (eq (suc zero))
act₀-cong (gate₂ CX-gate) eq (suc i) = eq (suc i)
act₀-cong (gate₂ SWAP-gate) eq zero = eq (suc zero)
act₀-cong (gate₂ SWAP-gate) eq (suc zero) = eq zero
act₀-cong (gate₂ SWAP-gate) eq (suc (suc i)) = eq (suc (suc i))
act₀-cong (gate₃ CCX-gate) eq zero =
  cong₂ _xor_ (eq zero) (cong₂ _∧_ (eq (suc zero)) (eq (suc (suc zero))))
act₀-cong (gate₃ CCX-gate) eq (suc i) = eq (suc i)
act₀-cong (g ↥) eq zero = eq zero
act₀-cong (g ↥) eq (suc i) = act₀-cong g (λ j → eq (suc j)) i

act-cong : ∀ (w : Circuit n) {s t} → s ≈s t → act w s ≈s act w t
act-cong [ g ]ʷ = act₀-cong g
act-cong ε eq = eq
act-cong (u • v) eq = act-cong u (act-cong v eq)

shift-correct : ∀ (w : Circuit n) s → act (w ↑) s ≈s shift (act w) s
shift-correct [ g ]ʷ s i = refl
shift-correct ε s zero = refl
shift-correct ε s (suc i) = refl
shift-correct (u • v) s zero = trans
  (shift-correct u (act (v ↑) s) zero) (shift-correct v s zero)
shift-correct (u • v) s (suc i) = trans
  (shift-correct u (act (v ↑) s) (suc i))
  (act-cong u (λ j → shift-correct v s (suc j)) i)

-- Expanding the syntax produces an actual circuit in the requested
-- alphabet.  There is no additional SWAP gate on the physical side.
physical₀ : Gen n → HH.Circuit n
physical₀ (gate₀ ())
physical₀ (gate₁ X-gate) = HH.X
physical₀ (gate₂ CX-gate) = HH.CX
physical₀ (gate₂ SWAP-gate) = HH.Ex
physical₀ (gate₃ CCX-gate) = HH.CCX
physical₀ (g ↥) = physical₀ g HH.↑

physical : Circuit n → HH.Circuit n
physical = physical₀ ʷ

-- Reuse the existing adjacent-swap synthesis of the symmetric group.
route₀ : S.Gen n → Circuit n
route₀ (S.gate₀ ())
route₀ (S.gate₁ ())
route₀ (S.gate₂ S.σ-gate) = [ gate₂ SWAP-gate ]ʷ
route₀ (g S.↥) = route₀ g ↑

route : S.Circuit n → Circuit n
route = route₀ ʷ

route₀-correct : ∀ (g : S.Gen n) s i →
  act (route₀ g) s i ≡ s (SI.⟦ g ⟧ᵍ ⟨$⟩ʳ i)
route₀-correct (S.gate₀ ()) s i
route₀-correct (S.gate₁ ()) s i
route₀-correct (S.gate₂ S.σ-gate) s zero = refl
route₀-correct (S.gate₂ S.σ-gate) s (suc zero) = refl
route₀-correct (S.gate₂ S.σ-gate) s (suc (suc i)) = refl
route₀-correct (g S.↥) s zero = shift-correct (route₀ g) s zero
route₀-correct (g S.↥) s (suc i) = trans
  (shift-correct (route₀ g) s (suc i)) (route₀-correct g (lower s) i)

route-correct : ∀ (w : S.Circuit n) s i →
  act (route w) s i ≡ s (SI.⟦ w ⟧ ⟨$⟩ʳ i)
route-correct [ g ]ʷ = route₀-correct g
route-correct ε s i = refl
route-correct (u • v) s i = trans
  (route-correct u (act (route v) s) i)
  (route-correct v s (SI.⟦ u ⟧ ⟨$⟩ʳ i))
