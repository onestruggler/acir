------------------------------------------------------------------------
-- Presentations of groups
--
-- Qutrit Pauli operators and the action of Clifford circuits on them by
-- conjugation
--
-- A Pauli operator on n wires is ω^σ X^a₀ Z^b₀ ⊗ … ⊗ X^aₙ₋₁ Z^bₙ₋₁, a
-- phase σ and a vector of letters (a , b), all in ℤ/3, wire 0 first,
-- with X|j⟩ = |j + 1⟩, Z|j⟩ = ω^j |j⟩, so Z X = ω X Z.  A circuit C
-- acts by P ↦ C P C⁻¹ (act), its inverse by P ↦ C⁻¹ P C (act⁻).  For
-- the gates of Semantics (H ∝ [ω^{jk}], S = diag(ω, ω, 1), CZ =
-- diag(ω^{xy})): H X H⁻¹ = Z and H Z H⁻¹ = X², S X S⁻¹ = X Z² and S
-- fixes Z, CZ sends X on either wire to X times Z on the other, and −ω
-- acts trivially; so
--
--   H  : X^a Z^b ↦ ω^{2ab} X^{2b} Z^a,
--   S  : X^a Z^b ↦ ω^{a(a−1)} X^a Z^{b+2a},
--   CZ : X^a Z^b ⊗ X^c Z^d ↦ ω^{ac} X^a Z^{b+c} ⊗ X^c Z^{d+a},
--
-- and their inverses H⁻¹ : X^a Z^b ↦ ω^{2ab} X^b Z^{2a}, S⁻¹ : X^a Z^b
-- ↦ ω^{a(a−1)/2} X^a Z^{b+a}, CZ⁻¹ : ↦ ω^{2ac} X^a Z^{b+2c} ⊗ X^c
-- Z^{d+2a}.  (The enumerated lemmas are generated: qt/gen_pauli.pl.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.Pauli where

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Z3 public

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Pauli operators

-- X^a Z^b.
Letter : Set
Letter = Z3 × Z3

pattern 𝐈 = (𝟎 , 𝟎)
pattern 𝐗 = (𝟏 , 𝟎)
pattern 𝐙 = (𝟎 , 𝟏)

Pauli : ℕ → Set
Pauli n = Z3 × Vec Letter n

-- The phases picked up by S and its inverse: a (a − 1) and a (a − 1) / 2.
sφ sφ⁻ : Z3 → Z3
sφ  𝟎 = 𝟎
sφ  𝟏 = 𝟎
sφ  𝟐 = 𝟐
sφ⁻ 𝟎 = 𝟎
sφ⁻ 𝟏 = 𝟎
sφ⁻ 𝟐 = 𝟏

-- The action of a letter, and of its inverse.
actL actL⁻ : Gen n → Pauli n → Pauli n
actL (gate₀ ν-gate)  P                             = P
actL (gate₁ H-gate)  (σ , (a , b) ∷ ps)            = σ ⊞ 𝟐 ⊠ (a ⊠ b) , (𝟐 ⊠ b , a) ∷ ps
actL (gate₁ S-gate)  (σ , (a , b) ∷ ps)            = σ ⊞ sφ a , (a , b ⊞ 𝟐 ⊠ a) ∷ ps
actL (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps)  = σ ⊞ a ⊠ c , (a , b ⊞ c) ∷ (c , d ⊞ a) ∷ ps
actL (g ↥)           (σ , p ∷ ps)                  = proj₁ (actL g (σ , ps)) , p ∷ proj₂ (actL g (σ , ps))

actL⁻ (gate₀ ν-gate)  P                            = P
actL⁻ (gate₁ H-gate)  (σ , (a , b) ∷ ps)           = σ ⊞ 𝟐 ⊠ (a ⊠ b) , (b , 𝟐 ⊠ a) ∷ ps
actL⁻ (gate₁ S-gate)  (σ , (a , b) ∷ ps)           = σ ⊞ sφ⁻ a , (a , b ⊞ a) ∷ ps
actL⁻ (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) =
  σ ⊞ 𝟐 ⊠ (a ⊠ c) , (a , b ⊞ 𝟐 ⊠ c) ∷ (c , d ⊞ 𝟐 ⊠ a) ∷ ps
actL⁻ (g ↥)           (σ , p ∷ ps)                 = proj₁ (actL⁻ g (σ , ps)) , p ∷ proj₂ (actL⁻ g (σ , ps))

-- The action of a circuit, its rightmost letter acting first, and of
-- its inverse, its leftmost letter first.
act act⁻ : Circuit n → Pauli n → Pauli n
act [ g ]ʷ  P = actL g P
act ε       P = P
act (w • v) P = act w (act v P)

act⁻ [ g ]ʷ  P = actL⁻ g P
act⁻ ε       P = P
act⁻ (w • v) P = act⁻ v (act⁻ w P)

------------------------------------------------------------------------
-- The two actions are inverse

private

  cancel₂ : ∀ x y → x ⊞ y ⊞ 𝟐 ⊠ y ≡ x
  cancel₂ 𝟎 𝟎 = refl
  cancel₂ 𝟎 𝟏 = refl
  cancel₂ 𝟎 𝟐 = refl
  cancel₂ 𝟏 𝟎 = refl
  cancel₂ 𝟏 𝟏 = refl
  cancel₂ 𝟏 𝟐 = refl
  cancel₂ 𝟐 𝟎 = refl
  cancel₂ 𝟐 𝟏 = refl
  cancel₂ 𝟐 𝟐 = refl

  cancel₂′ : ∀ x y → x ⊞ 𝟐 ⊠ y ⊞ y ≡ x
  cancel₂′ 𝟎 𝟎 = refl
  cancel₂′ 𝟎 𝟏 = refl
  cancel₂′ 𝟎 𝟐 = refl
  cancel₂′ 𝟏 𝟎 = refl
  cancel₂′ 𝟏 𝟏 = refl
  cancel₂′ 𝟏 𝟐 = refl
  cancel₂′ 𝟐 𝟎 = refl
  cancel₂′ 𝟐 𝟏 = refl
  cancel₂′ 𝟐 𝟐 = refl

  twice₂ : ∀ a → 𝟐 ⊠ (𝟐 ⊠ a) ≡ a
  twice₂ 𝟎 = refl
  twice₂ 𝟏 = refl
  twice₂ 𝟐 = refl

  H-phase : ∀ σ a b → σ ⊞ 𝟐 ⊠ (a ⊠ b) ⊞ 𝟐 ⊠ (𝟐 ⊠ b ⊠ a) ≡ σ
  H-phase 𝟎 𝟎 𝟎 = refl
  H-phase 𝟎 𝟎 𝟏 = refl
  H-phase 𝟎 𝟎 𝟐 = refl
  H-phase 𝟎 𝟏 𝟎 = refl
  H-phase 𝟎 𝟏 𝟏 = refl
  H-phase 𝟎 𝟏 𝟐 = refl
  H-phase 𝟎 𝟐 𝟎 = refl
  H-phase 𝟎 𝟐 𝟏 = refl
  H-phase 𝟎 𝟐 𝟐 = refl
  H-phase 𝟏 𝟎 𝟎 = refl
  H-phase 𝟏 𝟎 𝟏 = refl
  H-phase 𝟏 𝟎 𝟐 = refl
  H-phase 𝟏 𝟏 𝟎 = refl
  H-phase 𝟏 𝟏 𝟏 = refl
  H-phase 𝟏 𝟏 𝟐 = refl
  H-phase 𝟏 𝟐 𝟎 = refl
  H-phase 𝟏 𝟐 𝟏 = refl
  H-phase 𝟏 𝟐 𝟐 = refl
  H-phase 𝟐 𝟎 𝟎 = refl
  H-phase 𝟐 𝟎 𝟏 = refl
  H-phase 𝟐 𝟎 𝟐 = refl
  H-phase 𝟐 𝟏 𝟎 = refl
  H-phase 𝟐 𝟏 𝟏 = refl
  H-phase 𝟐 𝟏 𝟐 = refl
  H-phase 𝟐 𝟐 𝟎 = refl
  H-phase 𝟐 𝟐 𝟏 = refl
  H-phase 𝟐 𝟐 𝟐 = refl

  H-phase′ : ∀ σ a b → σ ⊞ 𝟐 ⊠ (a ⊠ b) ⊞ 𝟐 ⊠ (b ⊠ (𝟐 ⊠ a)) ≡ σ
  H-phase′ 𝟎 𝟎 𝟎 = refl
  H-phase′ 𝟎 𝟎 𝟏 = refl
  H-phase′ 𝟎 𝟎 𝟐 = refl
  H-phase′ 𝟎 𝟏 𝟎 = refl
  H-phase′ 𝟎 𝟏 𝟏 = refl
  H-phase′ 𝟎 𝟏 𝟐 = refl
  H-phase′ 𝟎 𝟐 𝟎 = refl
  H-phase′ 𝟎 𝟐 𝟏 = refl
  H-phase′ 𝟎 𝟐 𝟐 = refl
  H-phase′ 𝟏 𝟎 𝟎 = refl
  H-phase′ 𝟏 𝟎 𝟏 = refl
  H-phase′ 𝟏 𝟎 𝟐 = refl
  H-phase′ 𝟏 𝟏 𝟎 = refl
  H-phase′ 𝟏 𝟏 𝟏 = refl
  H-phase′ 𝟏 𝟏 𝟐 = refl
  H-phase′ 𝟏 𝟐 𝟎 = refl
  H-phase′ 𝟏 𝟐 𝟏 = refl
  H-phase′ 𝟏 𝟐 𝟐 = refl
  H-phase′ 𝟐 𝟎 𝟎 = refl
  H-phase′ 𝟐 𝟎 𝟏 = refl
  H-phase′ 𝟐 𝟎 𝟐 = refl
  H-phase′ 𝟐 𝟏 𝟎 = refl
  H-phase′ 𝟐 𝟏 𝟏 = refl
  H-phase′ 𝟐 𝟏 𝟐 = refl
  H-phase′ 𝟐 𝟐 𝟎 = refl
  H-phase′ 𝟐 𝟐 𝟏 = refl
  H-phase′ 𝟐 𝟐 𝟐 = refl

  S-phase : ∀ σ a → σ ⊞ sφ a ⊞ sφ⁻ a ≡ σ
  S-phase 𝟎 𝟎 = refl
  S-phase 𝟎 𝟏 = refl
  S-phase 𝟎 𝟐 = refl
  S-phase 𝟏 𝟎 = refl
  S-phase 𝟏 𝟏 = refl
  S-phase 𝟏 𝟐 = refl
  S-phase 𝟐 𝟎 = refl
  S-phase 𝟐 𝟏 = refl
  S-phase 𝟐 𝟐 = refl

  S-phase′ : ∀ σ a → σ ⊞ sφ⁻ a ⊞ sφ a ≡ σ
  S-phase′ 𝟎 𝟎 = refl
  S-phase′ 𝟎 𝟏 = refl
  S-phase′ 𝟎 𝟐 = refl
  S-phase′ 𝟏 𝟎 = refl
  S-phase′ 𝟏 𝟏 = refl
  S-phase′ 𝟏 𝟐 = refl
  S-phase′ 𝟐 𝟎 = refl
  S-phase′ 𝟐 𝟏 = refl
  S-phase′ 𝟐 𝟐 = refl

actL⁻-actL : (g : Gen n) (P : Pauli n) → actL⁻ g (actL g P) ≡ P
actL⁻-actL (gate₀ ν-gate) P = refl
actL⁻-actL (gate₁ H-gate) (σ , (a , b) ∷ ps) =
  Eq.cong₂ (λ x y → x , (a , y) ∷ ps) (H-phase σ a b) (twice₂ b)
actL⁻-actL (gate₁ S-gate) (σ , (a , b) ∷ ps) =
  Eq.cong₂ (λ x y → x , (a , y) ∷ ps) (S-phase σ a) (cancel₂′ b a)
actL⁻-actL (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) =
  Eq.cong₂ _,_ (cancel₂ σ (a ⊠ c))
    (Eq.cong₂ (λ x y → (a , x) ∷ (c , y) ∷ ps) (cancel₂ b c) (cancel₂ d a))
actL⁻-actL (g ↥) (σ , p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL⁻-actL g (σ , ps)))
                                (Eq.cong proj₂ (actL⁻-actL g (σ , ps)))

actL-actL⁻ : (g : Gen n) (P : Pauli n) → actL g (actL⁻ g P) ≡ P
actL-actL⁻ (gate₀ ν-gate) P = refl
actL-actL⁻ (gate₁ H-gate) (σ , (a , b) ∷ ps) =
  Eq.cong₂ (λ x y → x , (y , b) ∷ ps) (H-phase′ σ a b) (twice₂ a)
actL-actL⁻ (gate₁ S-gate) (σ , (a , b) ∷ ps) =
  Eq.cong₂ (λ x y → x , (a , y) ∷ ps) (S-phase′ σ a) (cancel₂ b a)
actL-actL⁻ (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) =
  Eq.cong₂ _,_ (cancel₂′ σ (a ⊠ c))
    (Eq.cong₂ (λ x y → (a , x) ∷ (c , y) ∷ ps) (cancel₂′ b c) (cancel₂′ d a))
actL-actL⁻ (g ↥) (σ , p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL-actL⁻ g (σ , ps)))
                                (Eq.cong proj₂ (actL-actL⁻ g (σ , ps)))

act⁻-act : (w : Circuit n) (P : Pauli n) → act⁻ w (act w P) ≡ P
act⁻-act [ g ]ʷ  P = actL⁻-actL g P
act⁻-act ε       P = refl
act⁻-act (w • v) P = Eq.trans (Eq.cong (act⁻ v) (act⁻-act w (act v P))) (act⁻-act v P)

act-act⁻ : (w : Circuit n) (P : Pauli n) → act w (act⁻ w P) ≡ P
act-act⁻ [ g ]ʷ  P = actL-actL⁻ g P
act-act⁻ ε       P = refl
act-act⁻ (w • v) P = Eq.trans (Eq.cong (act w) (act-act⁻ v (act⁻ w P))) (act-act⁻ w P)

------------------------------------------------------------------------
-- Circuits one wire up act on the wires above

act-↑ : (w : Circuit n) (σ : Z3) (p : Letter) (ps : Vec Letter n) →
        act (w ↑) (σ , p ∷ ps) ≡ (proj₁ (act w (σ , ps)) , p ∷ proj₂ (act w (σ , ps)))
act-↑ [ g ]ʷ  σ p ps = refl
act-↑ ε       σ p ps = refl
act-↑ (w • v) σ p ps = Eq.trans (Eq.cong (act (w ↑)) (act-↑ v σ p ps))
  (act-↑ w (proj₁ (act v (σ , ps))) p (proj₂ (act v (σ , ps))))

act⁻-↑ : (w : Circuit n) (σ : Z3) (p : Letter) (ps : Vec Letter n) →
         act⁻ (w ↑) (σ , p ∷ ps) ≡ (proj₁ (act⁻ w (σ , ps)) , p ∷ proj₂ (act⁻ w (σ , ps)))
act⁻-↑ [ g ]ʷ  σ p ps = refl
act⁻-↑ ε       σ p ps = refl
act⁻-↑ (w • v) σ p ps = Eq.trans (Eq.cong (act⁻ (v ↑)) (act⁻-↑ w σ p ps))
  (act⁻-↑ v (proj₁ (act⁻ w (σ , ps))) p (proj₂ (act⁻ w (σ , ps))))

-- The identity operator is fixed by every circuit.
I^ : (n : ℕ) → Vec Letter n
I^ n = replicate n 𝐈

actL⁻-I : (g : Gen n) (σ : Z3) → actL⁻ g (σ , I^ n) ≡ (σ , I^ n)
actL⁻-I (gate₀ ν-gate)  σ = refl
actL⁻-I (gate₁ H-gate)  σ = Eq.cong (_, _) (⊞-identityʳ σ)
actL⁻-I (gate₁ S-gate)  σ = Eq.cong (_, _) (⊞-identityʳ σ)
actL⁻-I (gate₂ CZ-gate) σ = Eq.cong (_, _) (⊞-identityʳ σ)
actL⁻-I {suc n} (g ↥) σ =
  Eq.cong₂ (λ x y → x , 𝐈 ∷ y) (Eq.cong proj₁ (actL⁻-I g σ)) (Eq.cong proj₂ (actL⁻-I g σ))

act⁻-I : (w : Circuit n) (σ : Z3) → act⁻ w (σ , I^ n) ≡ (σ , I^ n)
act⁻-I [ g ]ʷ  σ = actL⁻-I g σ
act⁻-I ε       σ = refl
act⁻-I (w • v) σ = Eq.trans (Eq.cong (act⁻ v) (act⁻-I w σ)) (act⁻-I v σ)
