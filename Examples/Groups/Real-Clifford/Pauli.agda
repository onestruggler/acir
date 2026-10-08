------------------------------------------------------------------------
-- Presentations of groups
--
-- Signed Pauli operators and the action of real Clifford circuits on
-- them by conjugation
--
-- A Pauli operator on n wires is ±X^a₀ Z^b₀ ⊗ … ⊗ X^aₙ₋₁ Z^bₙ₋₁, a sign
-- and a vector of pairs (a , b) of bits, wire 0 first.  A circuit C acts
-- by P ↦ C P C⁻¹: H swaps X and Z (X Z ↦ Z X = −X Z), Z negates X,
-- and CZ multiplies X on one wire by Z on the other.  Every letter is
-- an involution here as in the group, so the inverse of a circuit acts
-- by the inverse map (act-inv).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Pauli where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Pauli operators

Letter : Set
Letter = Bool × Bool

pattern 𝐈  = (false , false)
pattern 𝐗  = (true , false)
pattern 𝐙  = (false , true)
pattern 𝐘  = (true , true)   -- X Z

Pauli : ℕ → Set
Pauli n = Bool × Vec Letter n

-- The action of a letter.
actL : Gen n → Pauli n → Pauli n
actL (gate₀ neg-gate) P = P
actL (gate₁ H-gate)  (σ , (a , b) ∷ ps)           = σ xor (a ∧ b) , (b , a) ∷ ps
actL (gate₁ Z-gate)  (σ , (a , b) ∷ ps)           = σ xor a , (a , b) ∷ ps
actL (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) = σ xor (a ∧ c) , (a , b xor c) ∷ (c , d xor a) ∷ ps
actL (g ↥)           (σ , p ∷ ps)                 = proj₁ (actL g (σ , ps)) , p ∷ proj₂ (actL g (σ , ps))

-- The action of a circuit: its rightmost letter acts first.
act : Circuit n → Pauli n → Pauli n
act [ g ]ʷ  P = actL g P
act ε       P = P
act (w • v) P = act w (act v P)

-- The inverse of a circuit: its letters reversed.
inv : Circuit n → Circuit n
inv [ g ]ʷ  = [ g ]ʷ
inv ε       = ε
inv (w • v) = inv v • inv w

------------------------------------------------------------------------
-- Every letter acts by an involution

private
  xx : (σ a : Bool) → (σ xor a) xor a ≡ σ
  xx false false = Eq.refl
  xx true  false = Eq.refl
  xx false true  = Eq.refl
  xx true  true  = Eq.refl

  xor-false : (σ : Bool) → σ xor false ≡ σ
  xor-false false = Eq.refl
  xor-false true  = Eq.refl

actL-invol : (g : Gen n) (P : Pauli n) → actL g (actL g P) ≡ P
actL-invol (gate₀ neg-gate) P = Eq.refl
actL-invol (gate₁ H-gate) (σ , (false , false) ∷ ps) = Eq.cong (_, _) (Eq.trans (xor-false _) (xor-false σ))
actL-invol (gate₁ H-gate) (σ , (false , true) ∷ ps)  = Eq.cong (_, _) (Eq.trans (xor-false _) (xor-false σ))
actL-invol (gate₁ H-gate) (σ , (true , false) ∷ ps)  = Eq.cong (_, _) (Eq.trans (xor-false _) (xor-false σ))
actL-invol (gate₁ H-gate) (σ , (true , true) ∷ ps)   = Eq.cong (_, _) (xx σ true)
actL-invol (gate₁ Z-gate) (σ , (a , b) ∷ ps)         = Eq.cong (_, _) (xx σ a)
actL-invol (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) =
  Eq.cong₂ _,_ (xx σ (a ∧ c)) (Eq.cong₂ (λ x y → (a , x) ∷ (c , y) ∷ ps) (xx b c) (xx d a))
actL-invol (g ↥) (σ , p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL-invol g (σ , ps))) (Eq.cong proj₂ (actL-invol g (σ , ps)))

act-inv : (w : Circuit n) (P : Pauli n) → act (inv w) (act w P) ≡ P
act-inv [ g ]ʷ  P = actL-invol g P
act-inv ε       P = Eq.refl
act-inv (w • v) P = Eq.trans (Eq.cong (act (inv v)) (act-inv w (act v P))) (act-inv v P)

inv-act : (w : Circuit n) (P : Pauli n) → act w (act (inv w) P) ≡ P
inv-act [ g ]ʷ  P = actL-invol g P
inv-act ε       P = Eq.refl
inv-act (w • v) P = Eq.trans (Eq.cong (act w) (inv-act v (act (inv w) P))) (inv-act w P)

-- Acting is injective.
act-injective : (w : Circuit n) {P Q : Pauli n} → act w P ≡ act w Q → P ≡ Q
act-injective w {P} {Q} e =
  Eq.trans (Eq.sym (act-inv w P)) (Eq.trans (Eq.cong (act (inv w)) e) (act-inv w Q))

------------------------------------------------------------------------
-- Circuits one wire up act on the wires above

act-↑ : (w : Circuit n) (σ : Bool) (p : Letter) (ps : Vec Letter n) →
        act (w ↑) (σ , p ∷ ps) ≡ (proj₁ (act w (σ , ps)) , p ∷ proj₂ (act w (σ , ps)))
act-↑ [ g ]ʷ  σ p ps = Eq.refl
act-↑ ε       σ p ps = Eq.refl
act-↑ (w • v) σ p ps = Eq.trans (Eq.cong (act (w ↑)) (act-↑ v σ p ps))
  (act-↑ w (proj₁ (act v (σ , ps))) p (proj₂ (act v (σ , ps))))

inv-↑ : (w : Circuit n) → inv (w ↑) ≡ inv w ↑
inv-↑ [ g ]ʷ  = Eq.refl
inv-↑ ε       = Eq.refl
inv-↑ (w • v) = Eq.cong₂ _•_ (inv-↑ v) (inv-↑ w)

-- The identity operator is fixed by every circuit.
I^ : (n : ℕ) → Vec Letter n
I^ n = replicate n 𝐈

actL-I : (g : Gen n) (σ : Bool) → actL g (σ , I^ n) ≡ (σ , I^ n)
actL-I (gate₀ neg-gate) σ = Eq.refl
actL-I (gate₁ H-gate)  σ = Eq.cong (_, _) (xor-false σ)
actL-I (gate₁ Z-gate)  σ = Eq.cong (_, _) (xor-false σ)
actL-I (gate₂ CZ-gate) σ = Eq.cong (_, _) (xor-false σ)
actL-I {suc n} (g ↥) σ =
  Eq.cong₂ (λ x y → x , 𝐈 ∷ y) (Eq.cong proj₁ (actL-I g σ)) (Eq.cong proj₂ (actL-I g σ))

act-I : (w : Circuit n) (σ : Bool) → act w (σ , I^ n) ≡ (σ , I^ n)
act-I [ g ]ʷ  σ = actL-I g σ
act-I ε       σ = Eq.refl
act-I (w • v) σ = Eq.trans (Eq.cong (act w) (act-I v σ)) (act-I w σ)

-- The sign goes along: σ is added to what the circuit does to +P.
actL-sign : (g : Gen n) (σ : Bool) (ps : Vec Letter n) →
            actL g (σ , ps) ≡ (σ xor proj₁ (actL g (false , ps)) , proj₂ (actL g (false , ps)))
actL-sign (gate₀ neg-gate) σ ps = Eq.cong (_, ps) (Eq.sym (xor-false σ))
actL-sign (gate₁ H-gate) σ ((a , b) ∷ ps) = Eq.refl
actL-sign (gate₁ Z-gate) σ ((a , b) ∷ ps) = Eq.refl
actL-sign (gate₂ CZ-gate) σ ((a , b) ∷ (c , d) ∷ ps) = Eq.refl
actL-sign (g ↥) σ (p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL-sign g σ ps)) (Eq.cong proj₂ (actL-sign g σ ps))
