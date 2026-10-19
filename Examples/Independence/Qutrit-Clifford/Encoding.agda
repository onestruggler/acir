------------------------------------------------------------------------
-- Presentations of groups
--
-- Cliff₃'s circuits as Paper-V0 circuits, up to a phase
--
-- E₀ sends Blake's qutrit gates to Paper-V0 words of the same matrix up
-- to a power of ω₁₂: ω₁₂ to ε, H and S to themselves (V0Mat reads them
-- as Blake's matrices), the CNOT (control on wire 1) to H³ CZ H on
-- wire 0, and the swap to Paper-V0's swap.  Cliff₃'s words are in diagram
-- order and Paper-V0's in operator order, so E₀ reverses a word.  Its
-- matrix is then the circuit's up to a phase (enc-sem), and so circuits
-- with equal matrices have encodings equal by Paper-V0's rules
-- (Bridge).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Encoding where

open import Data.Nat.Base using (ℕ ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt ; ⊤)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Examples.Independence.Semantics.Qutrit
open import Algebra.Bundles using (CommutativeRing)
open CommutativeRing R using (*-identityˡ ; *-identityʳ)
open import Examples.Independence.Qutrit-Clifford.Weyl using (CZᵍ)
open import Examples.Independence.Qutrit-Clifford.V0Mat using (M₀ ; M)
open import Examples.Independence.Qutrit-Clifford.Faithful using (M-↥)
import Examples.Independence.Qutrit-Clifford.P3 as P3

import Examples.Groups.Symplectic.Syntactics.Gates 1 P3.p-prime as Gates
module V = Gates.Symplectic
open V using (gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate) renaming (Gen to VGen ; _↥ to _↥ᵛ)
open import Circuit.Base Gates.Symplectic.SympGate using (_↧ᵏ_ ; _↓ᵏ_)

open import Examples.Independence.Qutrit-Clifford.Syntactics as C
  using (Gen ; Circuit ; gate₀ ; gate₃ ; ⌈_⌉ ; swap ; ω-gate ; CX-gate)
  renaming (H-gate to H-gateᶜ ; S-gate to S-gateᶜ ; gate₁ to gate₁ᶜ ; gate₂ to gate₂ᶜ ; _↥ to _↥ᶜ)
import Examples.Independence.Qutrit-Clifford.Semantics as Sem

open Phases (λ _ → ⊤) tt (λ _ _ → tt) (λ _ → tt)
  using (≐→≈ ; ≈-refl ; ≈-sym ; ≈-trans ; ∙-cong ; ↑s-cong ; embs-cong ; phased)
  renaming (_≈_ to _≈ᵖ_)
open Decide (λ _ → ⊤) tt (λ _ _ → tt) (λ _ → tt) using (check)

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- A word on the bottom wires of a wider circuit

private
  M₀-scale : (g : VGen k) (n : ℕ) → proj₁ (M₀ (g ↧ᵏ n)) ≡ proj₁ (M₀ g)
  M₀-scale (gate₁ H-gate)  n = refl
  M₀-scale (gate₁ S-gate)  n = refl
  M₀-scale (gate₂ CZ-gate) n = refl
  M₀-scale (g ↥ᵛ)          n = M₀-scale g n

  M₀-↧ : (g : VGen k) (n : ℕ) → ix (proj₂ (M₀ (g ↧ᵏ n))) ≐ emb {k} {n} (ix (proj₂ (M₀ g)))
  M₀-↧ {suc k} (gate₁ H-gate) n =
    ≐-trans (ix-emb {1} {k +ℕ n} (proj₂ Hᵍ))
      (≐-trans (emb-pad₁ {k} {n} (ix (proj₂ Hᵍ)))
        (emb-cong {suc k} {n} (≐-sym (ix-emb {1} {k} (proj₂ Hᵍ)))))
  M₀-↧ {suc k} (gate₁ S-gate) n =
    ≐-trans (ix-emb {1} {k +ℕ n} (proj₂ Sᵍ))
      (≐-trans (emb-pad₁ {k} {n} (ix (proj₂ Sᵍ)))
        (emb-cong {suc k} {n} (≐-sym (ix-emb {1} {k} (proj₂ Sᵍ)))))
  M₀-↧ {suc (suc k)} (gate₂ CZ-gate) n =
    ≐-trans (ix-emb {2} {k +ℕ n} (proj₂ CZᵍ))
      (≐-trans (emb-pad₂ {k} {n} (ix (proj₂ CZᵍ)))
        (emb-cong {suc (suc k)} {n} (≐-sym (ix-emb {2} {k} (proj₂ CZᵍ)))))
  M₀-↧ {suc k} (g ↥ᵛ) n =
    ≐-trans (ix-up (proj₂ (M₀ (g ↧ᵏ n))))
      (≐-trans (up-cong (M₀-↧ g n))
        (≐-trans (up-emb {k} {n} (ix (proj₂ (M₀ g))))
          (emb-cong {suc k} {n} (≐-sym (ix-up (proj₂ (M₀ g)))))))

M-scale : (u : Word (VGen k)) (n : ℕ) → proj₁ (M (u ↓ᵏ n)) ≡ proj₁ (M u)
M-scale [ g ]ʷ  n = M₀-scale g n
M-scale ε       n = refl
M-scale (u • v) n = Eq.cong₂ _+ℕ_ (M-scale v n) (M-scale u n)

M-↓ : (u : Word (VGen k)) (n : ℕ) → ix (proj₂ (M (u ↓ᵏ n))) ≐ emb {k} {n} (ix (proj₂ (M u)))
M-↓ [ g ]ʷ  n = M₀-↧ g n
M-↓ {k} ε   n = ≐-trans ix-id (≐-trans (≐-sym (emb-id {k} {n})) (emb-cong {k} {n} (≐-sym ix-id)))
M-↓ {k} (u • v) n =
  ≐-trans (ix-mul (proj₂ (M (u ↓ᵏ n))) (proj₂ (M (v ↓ᵏ n))))
    (≐-trans (⊙-cong (M-↓ u n) (M-↓ v n))
      (≐-trans (emb-⊙ {k} {n} (ix (proj₂ (M u))) (ix (proj₂ (M v))))
        (emb-cong {k} {n} (≐-sym (ix-mul (proj₂ (M u)) (proj₂ (M v)))))))

M-↓≈ : (u : Word (VGen k)) (n : ℕ) → embs {k} {n} (M u) ≈ᵖ M (u ↓ᵏ n)
M-↓≈ {k} u n =
  ≐→≈ {s = embs {k} {n} (M u)} {M (u ↓ᵏ n)} (Eq.sym (M-scale u n))
    (≐-trans (ix-emb {k} {n} (proj₂ (M u))) (≐-sym (M-↓ u n)))

------------------------------------------------------------------------
-- The encoding

-- H³ CZ H on wire 0, controlled on wire 1, in operator order: the
-- CNOT |b₀ , b₁⟩ ↦ |b₀ + b₁ , b₁⟩.
CX₂ : Word (VGen 2)
CX₂ = [ gate₁ H-gate ]ʷ • ([ gate₁ H-gate ]ʷ • ([ gate₁ H-gate ]ʷ •
        ([ gate₂ CZ-gate ]ʷ • [ gate₁ H-gate ]ʷ)))

-- The swap: Paper-V0's own, CZ (H ⊗ H) three times, which is exactly
-- the swap matrix.
SW₂ : Word (VGen 2)
SW₂ = V.Ex

E₀ : Gen n → Word (VGen n)
E₀ (gate₀ ⌈ ω-gate ⌉)       = ε
E₀ (gate₁ᶜ ⌈ H-gateᶜ ⌉)     = [ gate₁ H-gate ]ʷ
E₀ (gate₁ᶜ ⌈ S-gateᶜ ⌉)     = [ gate₁ S-gate ]ʷ
E₀ {suc (suc n)} (gate₂ᶜ ⌈ CX-gate ⌉) = CX₂ ↓ᵏ n
E₀ {suc (suc n)} (gate₂ᶜ swap)        = SW₂ ↓ᵏ n
E₀ (gate₃ ⌈ () ⌉)
E₀ (g ↥ᶜ)                   = wmap _↥ᵛ (E₀ g)

-- Reversing the word: Cliff₃ reads it in diagram order.
E₀ʷ : Circuit n → Word (VGen n)
E₀ʷ [ g ]ʷ  = E₀ g
E₀ʷ ε       = ε
E₀ʷ (w • v) = E₀ʷ v • E₀ʷ w

------------------------------------------------------------------------
-- Its matrix, up to a phase

private
  cx-local : Sem.⟦ [ gate₂ᶜ {0} ⌈ CX-gate ⌉ ]ʷ ⟧ ≈ᵖ M CX₂
  cx-local = check 0 tt _ _ _

  sw-local : Sem.⟦ [ gate₂ᶜ {0} swap ]ʷ ⟧ ≈ᵖ M SW₂
  sw-local = check 0 tt _ _ _

  ω-phase : Sem.⟦ [ gate₀ {n} ⌈ ω-gate ⌉ ]ʷ ⟧ ≈ᵖ εs
  ω-phase {n} = phased 1 tt λ i j → begin
    1# * ix (scalM {n} x) i j        ≡⟨ Eq.cong (1# *_) (ix-scalM x i j) ⟩
    1# * (x * δv i j)                ≡⟨ *-identityˡ _ ⟩
    x * δv i j                       ≡⟨ Eq.cong (x *_) (Eq.sym (ix-id i j)) ⟩
    x * ix (idM {n}) i j             ≡⟨ Eq.cong (_* ix (idM {n}) i j)
                                          (Eq.sym (Eq.trans (*-identityʳ (x * 1#)) (*-identityʳ x))) ⟩
    ((x * 1#) * 1#) * ix (idM {n}) i j ∎
    where open Eq.≡-Reasoning

  M-↥-scale : (w : Word (VGen n)) → proj₁ (M (wmap _↥ᵛ w)) ≡ proj₁ (M w)
  M-↥-scale [ g ]ʷ  = refl
  M-↥-scale ε       = refl
  M-↥-scale (u • v) = Eq.cong₂ _+ℕ_ (M-↥-scale v) (M-↥-scale u)

  M-↥≈ : (w : Word (VGen n)) → ↑s (M w) ≈ᵖ M (wmap _↥ᵛ w)
  M-↥≈ w = ≐→≈ {s = ↑s (M w)} {M (wmap _↥ᵛ w)} (Eq.sym (M-↥-scale w))
             (≐-trans (ix-up (proj₂ (M w))) (≐-sym (M-↥ w)))

enc₀ : (g : Gen n) → Sem.⟦ [ g ]ʷ ⟧ ≈ᵖ M (E₀ g)
enc₀ (gate₀ ⌈ ω-gate ⌉)   = ω-phase
enc₀ (gate₁ᶜ ⌈ H-gateᶜ ⌉) = ≈-refl
enc₀ (gate₁ᶜ ⌈ S-gateᶜ ⌉) = ≈-refl
enc₀ {suc (suc n)} (gate₂ᶜ ⌈ CX-gate ⌉) =
  ≈-trans (embs-cong {2} {n} cx-local) (M-↓≈ CX₂ n)
enc₀ {suc (suc n)} (gate₂ᶜ swap) =
  ≈-trans (embs-cong {2} {n} sw-local) (M-↓≈ SW₂ n)
enc₀ (gate₃ ⌈ () ⌉)
enc₀ (g ↥ᶜ) = ≈-trans (↑s-cong (enc₀ g)) (M-↥≈ (E₀ g))

-- Every circuit.
enc-sem : (w : Circuit n) → Sem.⟦ w ⟧ ≈ᵖ M (E₀ʷ w)
enc-sem [ g ]ʷ  = enc₀ g
enc-sem ε       = ≈-refl
enc-sem (w • v) = ∙-cong (enc-sem w) (enc-sem v)
