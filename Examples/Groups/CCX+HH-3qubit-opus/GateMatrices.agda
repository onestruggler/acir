------------------------------------------------------------------------
-- Presentations of groups
--
-- Each gate denotes its usual matrix.  Basis state i is the bit string
-- x₀x₁x₂ with i = 4x₀ + 2x₁ + x₂ (qubit 0 the most significant), and
-- the entry (r, c) of each gate is given by a formula in the bits of r
-- and c:
--
--   a permutation gate (X_j, CX_{j,k}, CCX_{j,k}, σ_{j,k}) has entry 1
--   where r is the image of c;
--   a diagonal gate (Z_j, CZ_{j,k}, CCZ) has entry -1 at the states it
--   negates and 1 elsewhere on the diagonal;
--   K_{j,k} = H_j H_k has entry ±1/2 where r and c agree off qubits j
--   and k, the sign (-1)^(r_j c_j + r_k c_k);
--   K_[0,1,2,3] is K₁₂ where r₀ = c₀ = 0 and the identity where
--   r₀ = c₀ = 1;
--   H₂ has entry ±1/√2 where r and c agree on qubits 0 and 1, the sign
--   (-1)^(r₂ c₂).
--
-- gate-matrix and gate-matrixᴴ check, by computation, that the
-- semantics (Semantics) gives each gate this matrix, over 𝔻 for the
-- gates of Σ₁ and over ℤ[1/√2] for those of Σ₂.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.GateMatrices where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _xor_ ; not)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Quantum.Synthesis.Ring using (Dyadic' ; RootTwo)
open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using ([_]ʷ)
import Examples.Groups.CCX+HH-TwoLevel.Ring as R1
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂ ; mk)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SL

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Bits

Bits : Set
Bits = Bool × Bool × Bool

bits : Fin 8 → Bits
bits zero = false , false , false
bits (suc zero) = false , false , true
bits (suc (suc zero)) = false , true , false
bits (suc (suc (suc zero))) = false , true , true
bits (suc (suc (suc (suc zero)))) = true , false , false
bits (suc (suc (suc (suc (suc zero))))) = true , false , true
bits (suc (suc (suc (suc (suc (suc zero)))))) = true , true , false
bits (suc (suc (suc (suc (suc (suc (suc _))))))) = true , true , true

_==_ : Bool → Bool → Bool
a == b = not (a xor b)

_≡ᵇ_ : Bits → Bits → Bool
(a , b , c) ≡ᵇ (a′ , b′ , c′) = (a == a′) ∧ ((b == b′) ∧ (c == c′))

------------------------------------------------------------------------
-- The entries

-- 0, ±1, ±1/2 and ±1/√2.
data Coef : Set where
  c0 c1 c-1 c½ c-½ cs c-s : Coef

sign : Bool → Coef → Coef
sign false c = c
sign true c1 = c-1
sign true c½ = c-½
sign true cs = c-s
sign true c = c

-- The permutation gates, as maps of bit strings.
perm : Gate k → Bits → Bits
perm X₀ (a , b , c) = not a , b , c
perm X₁ (a , b , c) = a , not b , c
perm X₂ (a , b , c) = a , b , not c
perm CX₀₁ (a , b , c) = a , (a xor b) , c
perm CX₀₂ (a , b , c) = a , b , (a xor c)
perm CX₁₀ (a , b , c) = (b xor a) , b , c
perm CX₁₂ (a , b , c) = a , b , (b xor c)
perm CX₂₀ (a , b , c) = (c xor a) , b , c
perm CX₂₁ (a , b , c) = a , (c xor b) , c
perm CCX₀₁ (a , b , c) = a , b , ((a ∧ b) xor c)
perm CCX₀₂ (a , b , c) = a , ((a ∧ c) xor b) , c
perm CCX₁₂ (a , b , c) = ((b ∧ c) xor a) , b , c
perm SW₀₁ (a , b , c) = b , a , c
perm SW₀₂ (a , b , c) = c , b , a
perm SW₁₂ (a , b , c) = a , c , b
perm _ x = x

-- The diagonal gates, as the bit strings they negate.
neg : Gate k → Bits → Bool
neg Z₀ (a , b , c) = a
neg Z₁ (a , b , c) = b
neg Z₂ (a , b , c) = c
neg CZ₀₁ (a , b , c) = a ∧ b
neg CZ₀₂ (a , b , c) = a ∧ c
neg CZ₁₂ (a , b , c) = b ∧ c
neg CCZ (a , b , c) = a ∧ (b ∧ c)
neg _ _ = false

private
  pm : Gate k → Bits → Bits → Coef
  pm g r c = if r ≡ᵇ perm g c then c1 else c0

  dg : Gate k → Bits → Bits → Coef
  dg g r c = if r ≡ᵇ c then sign (neg g c) c1 else c0

  -- H ⊗ H on two qubits, the third (whose bits are p, q) fixed.
  hh : Bool → Bool → Bool → Bool → Bool → Bool → Coef
  hh p q x y x′ y′ = if p == q then sign ((x ∧ x′) xor (y ∧ y′)) c½ else c0

coef : Gate k → Bits → Bits → Coef
coef g@X₀ = pm g
coef g@X₁ = pm g
coef g@X₂ = pm g
coef g@Z₀ = dg g
coef g@Z₁ = dg g
coef g@Z₂ = dg g
coef g@CX₀₁ = pm g
coef g@CX₀₂ = pm g
coef g@CX₁₀ = pm g
coef g@CX₁₂ = pm g
coef g@CX₂₀ = pm g
coef g@CX₂₁ = pm g
coef g@CZ₀₁ = dg g
coef g@CZ₀₂ = dg g
coef g@CZ₁₂ = dg g
coef g@CCX₀₁ = pm g
coef g@CCX₀₂ = pm g
coef g@CCX₁₂ = pm g
coef K₀₁ (a , b , c) (a′ , b′ , c′) = hh c c′ a b a′ b′
coef K₁₂ (a , b , c) (a′ , b′ , c′) = hh a a′ b c b′ c′
coef g@SW₀₁ = pm g
coef g@SW₀₂ = pm g
coef g@SW₁₂ = pm g
coef NK (false , b , c) (false , b′ , c′) = hh true true b c b′ c′
coef NK (true , b , c) (true , b′ , c′) = if (b == b′) ∧ (c == c′) then c1 else c0
coef NK _ _ = c0
coef g@CCZ = dg g
coef H₂ (a , b , c) (a′ , b′ , c′) = if (a == a′) ∧ (b == b′) then sign (c ∧ c′) cs else c0

------------------------------------------------------------------------
-- The matrices

-- Over 𝔻 (the entries ±1/√2 do not occur below level 2).
⟪_⟫ᵒ : Coef → 𝔻
⟪ c0 ⟫ᵒ = R1.0ᴰ
⟪ c1 ⟫ᵒ = R1.1ᴰ
⟪ c-1 ⟫ᵒ = Dyadic' -[1+ 0 ] 0 _
⟪ c½ ⟫ᵒ = R1.½ᴰ
⟪ c-½ ⟫ᵒ = Dyadic' -[1+ 0 ] 1 _
⟪ cs ⟫ᵒ = R1.0ᴰ
⟪ c-s ⟫ᵒ = R1.0ᴰ

-- Over ℤ[1/√2].
⟪_⟫ᴴ : Coef → ℤ[1/√2]
⟪ c0 ⟫ᴴ = R2.0ᴰ
⟪ c1 ⟫ᴴ = R2.1ᴰ
⟪ c-1 ⟫ᴴ = R2.-1ᴰ
⟪ c½ ⟫ᴴ = RootTwo (Dyadic' (+ 1) 1 _) R1.0ᴰ
⟪ c-½ ⟫ᴴ = RootTwo (Dyadic' -[1+ 0 ] 1 _) R1.0ᴰ
⟪ cs ⟫ᴴ = R2.√½
⟪ c-s ⟫ᴴ = RootTwo R1.0ᴰ (Dyadic' -[1+ 0 ] 1 _)

gateᵒ : Gate k → Matrix 8 8 𝔻
gateᵒ g = mk λ r c → ⟪ coef g (bits r) (bits c) ⟫ᵒ

gateᴴ : Gate k → Matrix 8 8 ℤ[1/√2]
gateᴴ g = SL.mk λ r c → ⟪ coef g (bits r) (bits c) ⟫ᴴ

------------------------------------------------------------------------
-- The semantics gives them

opaque
  unfolding actV set₁ set₂ R1._+ᴰ_ R1._*ᴰ_ R1.-ᴰ_

  gate-matrix : (g : Gate 1) → ⟦ [ g ]ʷ ⟧ ≡ gateᵒ g
  gate-matrix X₀ = refl
  gate-matrix X₁ = refl
  gate-matrix X₂ = refl
  gate-matrix Z₀ = refl
  gate-matrix Z₁ = refl
  gate-matrix Z₂ = refl
  gate-matrix CX₀₁ = refl
  gate-matrix CX₀₂ = refl
  gate-matrix CX₁₀ = refl
  gate-matrix CX₁₂ = refl
  gate-matrix CX₂₀ = refl
  gate-matrix CX₂₁ = refl
  gate-matrix CZ₀₁ = refl
  gate-matrix CZ₀₂ = refl
  gate-matrix CZ₁₂ = refl
  gate-matrix CCX₀₁ = refl
  gate-matrix CCX₀₂ = refl
  gate-matrix CCX₁₂ = refl
  gate-matrix K₀₁ = refl
  gate-matrix K₁₂ = refl
  gate-matrix SW₀₁ = refl
  gate-matrix SW₀₂ = refl
  gate-matrix SW₁₂ = refl
  gate-matrix NK = refl
  gate-matrix CCZ = refl

opaque
  unfolding SL.actV SL.set₁ SL.set₂ R2._+ᴰ_ R2._*ᴰ_ R2.-ᴰ_

  gate-matrixᴴ : (g : Gate 2) → ⟦ [ g ]ʷ ⟧ᴴ ≡ gateᴴ g
  gate-matrixᴴ X₀ = refl
  gate-matrixᴴ X₁ = refl
  gate-matrixᴴ X₂ = refl
  gate-matrixᴴ Z₀ = refl
  gate-matrixᴴ Z₁ = refl
  gate-matrixᴴ Z₂ = refl
  gate-matrixᴴ CX₀₁ = refl
  gate-matrixᴴ CX₀₂ = refl
  gate-matrixᴴ CX₁₀ = refl
  gate-matrixᴴ CX₁₂ = refl
  gate-matrixᴴ CX₂₀ = refl
  gate-matrixᴴ CX₂₁ = refl
  gate-matrixᴴ CZ₀₁ = refl
  gate-matrixᴴ CZ₀₂ = refl
  gate-matrixᴴ CZ₁₂ = refl
  gate-matrixᴴ CCX₀₁ = refl
  gate-matrixᴴ CCX₀₂ = refl
  gate-matrixᴴ CCX₁₂ = refl
  gate-matrixᴴ K₀₁ = refl
  gate-matrixᴴ K₁₂ = refl
  gate-matrixᴴ SW₀₁ = refl
  gate-matrixᴴ SW₀₂ = refl
  gate-matrixᴴ SW₁₂ = refl
  gate-matrixᴴ NK = refl
  gate-matrixᴴ CCZ = refl
  gate-matrixᴴ H₂ = refl
