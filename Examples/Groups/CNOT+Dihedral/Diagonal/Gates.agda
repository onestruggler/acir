------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled phases CS and CCZ, and the local identities of the
-- splitting of phase gates
--
-- CS = ω^(2 x₀ x₁) and CCZ = ω^(4 x₀ x₁ x₂) are the monomials of the
-- multilinear expansion of a phase polynomial: in terms of parities,
--
--     x₀ ⊕ x₁ = x₀ + x₁ − 2 x₀ x₁,
--     x₀ ⊕ x₁ ⊕ x₂ = x₀ + x₁ + x₂ − 2 (x₀ x₁ + x₀ x₂ + x₁ x₂) + 4 x₀ x₁ x₂,
--
-- so CS = T • T ↑ • U⁷ and CCZ = V • T • T ↑ • T ↑ ↑ • U⁷ • U₀₂⁷ • (U ↑)⁷.
-- A CNOT conjugates CS into CS times a CS on its control and target
-- times a CCZ (one instance of R₉), and CCZ into CCZ times a CCZ on
-- the target (R₁₃, with R₈ on the six pairs of four wires): the step
-- that reduces a parity by one wire in Diagonal.Split.  Every identity
-- here is an equation of diagonal expressions, decided by
-- Diagonal.Calculus with the relation instances it needs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Gates where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Powers
open import Examples.Groups.CNOT+Dihedral.Linear.Base using (LGen ; cnot ; swap ; _↥ₗ ; ι)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Calculus

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The gates as diagonal expressions

dU : DE (₂₊ n)
dU = `c cnot `T

dV : DE (₃₊ n)
dV = `c (cnot ↥ₗ) dU

dU₀₂ : DE (₃₊ n)
dU₀₂ = `c swap (dU `↑)

dCS : DE (₂₊ n)
dCS = `T `• `T `↑ `• dU `^ 7

dCCZ : DE (₃₊ n)
dCCZ = dV `• `T `• `T `↑ `• `T `↑ `↑ `• dU `^ 7 `• dU₀₂ `^ 7 `• dU `↑ `^ 7

CS : Circuit (₂₊ n)
CS = ⟦ dCS ⟧ᴰ

CCZ : Circuit (₃₊ n)
CCZ = ⟦ dCCZ ⟧ᴰ

-- The rotations of three wires that carry wires 0, 1 to 1, 2 and back.
πL πR : Circuit (₃₊ n)
πL = SWAP ↑ • SWAP
πR = SWAP • SWAP ↑

------------------------------------------------------------------------
-- The relations used, as expressions equal to ε

rel₈ : DE (₂₊ n)
rel₈ = rel (dU `^ 4) (`T `^ 4 `• `T `↑ `^ 4)

rel₈-ε : (₂₊ n) ⊢ ⟦ rel₈ ⟧ᴰ ≈ ε
rel₈-ε = rel-ε (dU `^ 4) (`T `^ 4 `• `T `↑ `^ 4) (ax R₈)

private
  dR₉ : DE (₃₊ n)
  dR₉ = `T `^ 6 `• `T `↑ `^ 6 `• `T `↑ `↑ `^ 6 `• dU `↑ `^ 2 `• dU₀₂ `^ 2 `• dU `^ 2

rel₉ : DE (₃₊ n)
rel₉ = rel (dV `^ 2) dR₉

rel₉-ε : (₃₊ n) ⊢ ⟦ rel₉ ⟧ᴰ ≈ ε
rel₉-ε {n} = rel-ε (dV `^ 2) dR₉ (trans (Pow.pow-cong (₃₊ n) 2 (by-assoc Eq.refl)) (ax R₉))
  where open Width (₃₊ n)

private
  dU₁₃ dU₀₃ dV₀₂₃ dV₀₁₃ : DE (₄₊ n)
  dU₁₃  = `c (swap ↥ₗ) (dU `↑ `↑)
  dU₀₃  = `c swap (`c (swap ↥ₗ) (dU `↑ `↑))
  dV₀₂₃ = `c swap (dV `↑)
  dV₀₁₃ = `c (swap ↥ₗ) (`c swap (dV `↑))

  dL₁₃ dR₁₃ : DE (₄₊ n)
  dL₁₃ = `c (cnot ↥ₗ ↥ₗ) dV
  dR₁₃ = `T `^ 5 `• `T `↑ `^ 5 `• `T `↑ `↑ `^ 5 `• `T `↑ `↑ `↑ `^ 5 `•
         dU `↑ `↑ `^ 3 `• dU₁₃ `^ 3 `• dU₀₃ `^ 3 `• dU `↑ `^ 3 `• dU₀₂ `^ 3 `• dU `^ 3 `•
         dV `↑ `• dV₀₂₃ `• dV₀₁₃ `• dV

rel₁₃ : DE (₄₊ n)
rel₁₃ = rel dL₁₃ dR₁₃

rel₁₃-ε : (₄₊ n) ⊢ ⟦ rel₁₃ ⟧ᴰ ≈ ε
rel₁₃-ε {n} = rel-ε dL₁₃ dR₁₃ (trans (by-assoc Eq.refl) (trans (ax R₁₃) (by-assoc Eq.refl)))
  where open Width (₄₊ n)

-- R₈ on each pair of four wires.
private
  a₂ a₃ a₄ a₅ a₆ : DE (₄₊ n)
  a₂ = `c (swap ↥ₗ) rel₈
  a₃ = rel₈ `↑
  a₄ = rel₈ `↑ `↑
  a₅ = `c (swap ↥ₗ ↥ₗ) (rel₈ `↑)
  a₆ = `c (swap ↥ₗ ↥ₗ) (`c (swap ↥ₗ) rel₈)

rel₈⁴ : DE (₄₊ n)
rel₈⁴ = rel₈ `• a₂ `• a₃ `• a₄ `• a₅ `• a₆

rel₈⁴-ε : (₄₊ n) ⊢ ⟦ rel₈⁴ ⟧ᴰ ≈ ε
rel₈⁴-ε =
  •-ε rel₈ (a₂ `• a₃ `• a₄ `• a₅ `• a₆) rel₈-ε
  (•-ε a₂ (a₃ `• a₄ `• a₅ `• a₆) (conj-ε (swap ↥ₗ) rel₈ rel₈-ε)
  (•-ε a₃ (a₄ `• a₅ `• a₆) (up-ε rel₈ rel₈-ε)
  (•-ε a₄ (a₅ `• a₆) (up-ε (rel₈ `↑) (up-ε rel₈ rel₈-ε))
  (•-ε a₅ a₆ (conj-ε (swap ↥ₗ ↥ₗ) (rel₈ `↑) (up-ε rel₈ rel₈-ε))
             (conj-ε (swap ↥ₗ ↥ₗ) (`c (swap ↥ₗ) rel₈) (conj-ε (swap ↥ₗ) rel₈ rel₈-ε))))))

------------------------------------------------------------------------
-- The identities

-- U in terms of T and CS.
U-CS : (₂₊ n) ⊢ U ≈ T ↑ • T • CS ^ 7
U-CS = by-dnorm dU (`T `↑ `• `T `• dCS `^ 7) Eq.refl

-- CS on wires 0 and 2, two ways.
CS₀₂ : (₃₊ n) ⊢ SWAP ↑ • CS • SWAP ↑ ≈ SWAP • CS ↑ • SWAP
CS₀₂ = by-dnorm (`c (swap ↥ₗ) dCS) (`c swap (dCS `↑)) Eq.refl

-- A CNOT on the target of CS.
CNOT-CS : (₃₊ n) ⊢ CNOT ↑ • CS • CNOT ↑ ≈ CS • (SWAP • CS ↑ • SWAP) • CCZ
CNOT-CS = by-dnorm-with (`c (cnot ↥ₗ) dCS) (dCS `• `c swap (dCS `↑) `• dCCZ)
            rel₉ rel₉-ε Eq.refl

-- CCZ on wires 0, 1 and 3, two ways.
CCZ₀₁₃ : (₄₊ n) ⊢ SWAP ↑ ↑ • CCZ • SWAP ↑ ↑ ≈ πL • CCZ ↑ • πR
CCZ₀₁₃ {n} = trans (by-dnorm (`c (swap ↥ₗ ↥ₗ) dCCZ) (`c (swap ↥ₗ) (`c swap (dCCZ `↑))) Eq.refl)
                   (by-assoc Eq.refl)
  where open Width (₄₊ n)

-- A CNOT on a target of CCZ.
CNOT-CCZ : (₄₊ n) ⊢ CNOT ↑ ↑ • CCZ • CNOT ↑ ↑ ≈ CCZ • πL • CCZ ↑ • πR
CNOT-CCZ {n} =
  trans (by-dnorm-with (`c (cnot ↥ₗ ↥ₗ) dCCZ) (dCCZ `• `c (swap ↥ₗ) (`c swap (dCCZ `↑)))
           (rel₁₃ `^ 7 `• rel₈⁴) (•-ε (rel₁₃ `^ 7) rel₈⁴ (^-ε rel₁₃ 7 rel₁₃-ε) rel₈⁴-ε) Eq.refl)
        (by-assoc Eq.refl)
  where open Width (₄₊ n)

-- The orders.
CS⁴ : (₂₊ n) ⊢ CS ^ 4 ≈ ε
CS⁴ = by-dnorm-with (dCS `^ 4) `ε rel₈ rel₈-ε Eq.refl

CCZ² : (₃₊ n) ⊢ CCZ ^ 2 ≈ ε
CCZ² = by-dnorm-with (dCCZ `^ 2) `ε (rel₉ `^ 3) (^-ε rel₉ 3 rel₉-ε) Eq.refl
