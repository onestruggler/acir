------------------------------------------------------------------------
-- Presentations of groups
--
-- Pauli operators and the action of Clifford circuits on them by
-- conjugation
--
-- A Pauli operator on n wires is i^σ X^a₀ Z^b₀ ⊗ … ⊗ X^aₙ₋₁ Z^bₙ₋₁, a
-- phase σ in ℤ/4 and a vector of pairs (a , b) of bits, wire 0 first;
-- the letter (1 , 1) is X Z, so Y = i X Z.  A circuit C acts by
-- P ↦ C P C⁻¹ (act), and its inverse by P ↦ C⁻¹ P C (act⁻): H swaps X
-- and Z (X Z ↦ Z X = −X Z), S sends X to Y = i X Z and fixes Z, CZ
-- multiplies X on one wire by Z on the other, and ω acts trivially.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Pauli where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Qubit-Clifford.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Phases

data Ph : Set where
  p0 p1 p2 p3 : Ph

-- Multiplication by i, −1 and −i.
inc neg dec : Ph → Ph
inc p0 = p1
inc p1 = p2
inc p2 = p3
inc p3 = p0
neg p0 = p2
neg p1 = p3
neg p2 = p0
neg p3 = p1
dec p0 = p3
dec p1 = p0
dec p2 = p1
dec p3 = p2

-- Adding a phase.
infixl 6 _⊕_
_⊕_ : Ph → Ph → Ph
σ ⊕ p0 = σ
σ ⊕ p1 = inc σ
σ ⊕ p2 = neg σ
σ ⊕ p3 = dec σ

-- Subtracting it again.
minus : Ph → Ph
minus p0 = p0
minus p1 = p3
minus p2 = p2
minus p3 = p1

⊕-minus : (σ δ : Ph) → σ ⊕ δ ⊕ minus δ ≡ σ
⊕-minus p0 p0 = Eq.refl
⊕-minus p0 p1 = Eq.refl
⊕-minus p0 p2 = Eq.refl
⊕-minus p0 p3 = Eq.refl
⊕-minus p1 p0 = Eq.refl
⊕-minus p1 p1 = Eq.refl
⊕-minus p1 p2 = Eq.refl
⊕-minus p1 p3 = Eq.refl
⊕-minus p2 p0 = Eq.refl
⊕-minus p2 p1 = Eq.refl
⊕-minus p2 p2 = Eq.refl
⊕-minus p2 p3 = Eq.refl
⊕-minus p3 p0 = Eq.refl
⊕-minus p3 p1 = Eq.refl
⊕-minus p3 p2 = Eq.refl
⊕-minus p3 p3 = Eq.refl

⊕-cancel : (σ σ' δ : Ph) → σ ⊕ δ ≡ σ' ⊕ δ → σ ≡ σ'
⊕-cancel σ σ' δ e =
  Eq.trans (Eq.sym (⊕-minus σ δ)) (Eq.trans (Eq.cong (_⊕ minus δ) e) (⊕-minus σ' δ))

-- Phases added under a condition.
twice once once⁻ : Bool → Ph → Ph
twice false σ = σ
twice true  σ = neg σ
once  false σ = σ
once  true  σ = inc σ
once⁻ false σ = σ
once⁻ true  σ = dec σ

private
  neg-neg : (σ : Ph) → neg (neg σ) ≡ σ
  neg-neg p0 = Eq.refl
  neg-neg p1 = Eq.refl
  neg-neg p2 = Eq.refl
  neg-neg p3 = Eq.refl

  dec-inc : (σ : Ph) → dec (inc σ) ≡ σ
  dec-inc p0 = Eq.refl
  dec-inc p1 = Eq.refl
  dec-inc p2 = Eq.refl
  dec-inc p3 = Eq.refl

  inc-dec : (σ : Ph) → inc (dec σ) ≡ σ
  inc-dec p0 = Eq.refl
  inc-dec p1 = Eq.refl
  inc-dec p2 = Eq.refl
  inc-dec p3 = Eq.refl

twice-twice : (x : Bool) (σ : Ph) → twice x (twice x σ) ≡ σ
twice-twice false σ = Eq.refl
twice-twice true  σ = neg-neg σ

once⁻-once : (x : Bool) (σ : Ph) → once⁻ x (once x σ) ≡ σ
once⁻-once false σ = Eq.refl
once⁻-once true  σ = dec-inc σ

once-once⁻ : (x : Bool) (σ : Ph) → once x (once⁻ x σ) ≡ σ
once-once⁻ false σ = Eq.refl
once-once⁻ true  σ = inc-dec σ

------------------------------------------------------------------------
-- Pauli operators

Letter : Set
Letter = Bool × Bool

pattern 𝐈  = (false , false)
pattern 𝐗  = (true , false)
pattern 𝐙  = (false , true)
pattern 𝐘  = (true , true)   -- X Z

Pauli : ℕ → Set
Pauli n = Ph × Vec Letter n

-- The action of a letter, and of its inverse.
actL actL⁻ : Gen n → Pauli n → Pauli n
actL (gate₀ ω-gate) P = P
actL (gate₁ H-gate)  (σ , (a , b) ∷ ps)           = twice (a ∧ b) σ , (b , a) ∷ ps
actL (gate₁ S-gate)  (σ , (a , b) ∷ ps)           = once a σ , (a , b xor a) ∷ ps
actL (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) = twice (a ∧ c) σ , (a , b xor c) ∷ (c , d xor a) ∷ ps
actL (g ↥)           (σ , p ∷ ps)                 = proj₁ (actL g (σ , ps)) , p ∷ proj₂ (actL g (σ , ps))

actL⁻ (gate₀ ω-gate) P = P
actL⁻ (gate₁ H-gate)  (σ , (a , b) ∷ ps)           = twice (a ∧ b) σ , (b , a) ∷ ps
actL⁻ (gate₁ S-gate)  (σ , (a , b) ∷ ps)           = once⁻ a σ , (a , b xor a) ∷ ps
actL⁻ (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) = twice (a ∧ c) σ , (a , b xor c) ∷ (c , d xor a) ∷ ps
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
  xx : (b a : Bool) → (b xor a) xor a ≡ b
  xx false false = Eq.refl
  xx true  false = Eq.refl
  xx false true  = Eq.refl
  xx true  true  = Eq.refl

  ∧-comm : (a b : Bool) → a ∧ b ≡ b ∧ a
  ∧-comm false false = Eq.refl
  ∧-comm false true  = Eq.refl
  ∧-comm true  false = Eq.refl
  ∧-comm true  true  = Eq.refl

  H-twice : (a b : Bool) (σ : Ph) → twice (b ∧ a) (twice (a ∧ b) σ) ≡ σ
  H-twice a b σ = Eq.trans (Eq.cong (λ x → twice x (twice (a ∧ b) σ)) (∧-comm b a)) (twice-twice (a ∧ b) σ)

actL⁻-actL : (g : Gen n) (P : Pauli n) → actL⁻ g (actL g P) ≡ P
actL⁻-actL (gate₀ ω-gate) P = Eq.refl
actL⁻-actL (gate₁ H-gate) (σ , (a , b) ∷ ps) = Eq.cong (_, _) (H-twice a b σ)
actL⁻-actL (gate₁ S-gate) (σ , (a , b) ∷ ps) =
  Eq.cong₂ (λ x y → x , (a , y) ∷ ps) (once⁻-once a σ) (xx b a)
actL⁻-actL (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) =
  Eq.cong₂ _,_ (twice-twice (a ∧ c) σ) (Eq.cong₂ (λ x y → (a , x) ∷ (c , y) ∷ ps) (xx b c) (xx d a))
actL⁻-actL (g ↥) (σ , p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL⁻-actL g (σ , ps))) (Eq.cong proj₂ (actL⁻-actL g (σ , ps)))

actL-actL⁻ : (g : Gen n) (P : Pauli n) → actL g (actL⁻ g P) ≡ P
actL-actL⁻ (gate₀ ω-gate) P = Eq.refl
actL-actL⁻ (gate₁ H-gate) (σ , (a , b) ∷ ps) = Eq.cong (_, _) (H-twice a b σ)
actL-actL⁻ (gate₁ S-gate) (σ , (a , b) ∷ ps) =
  Eq.cong₂ (λ x y → x , (a , y) ∷ ps) (once-once⁻ a σ) (xx b a)
actL-actL⁻ (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) =
  Eq.cong₂ _,_ (twice-twice (a ∧ c) σ) (Eq.cong₂ (λ x y → (a , x) ∷ (c , y) ∷ ps) (xx b c) (xx d a))
actL-actL⁻ (g ↥) (σ , p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL-actL⁻ g (σ , ps))) (Eq.cong proj₂ (actL-actL⁻ g (σ , ps)))

act⁻-act : (w : Circuit n) (P : Pauli n) → act⁻ w (act w P) ≡ P
act⁻-act [ g ]ʷ  P = actL⁻-actL g P
act⁻-act ε       P = Eq.refl
act⁻-act (w • v) P = Eq.trans (Eq.cong (act⁻ v) (act⁻-act w (act v P))) (act⁻-act v P)

act-act⁻ : (w : Circuit n) (P : Pauli n) → act w (act⁻ w P) ≡ P
act-act⁻ [ g ]ʷ  P = actL-actL⁻ g P
act-act⁻ ε       P = Eq.refl
act-act⁻ (w • v) P = Eq.trans (Eq.cong (act w) (act-act⁻ v (act⁻ w P))) (act-act⁻ w P)

------------------------------------------------------------------------
-- Circuits one wire up act on the wires above

act-↑ : (w : Circuit n) (σ : Ph) (p : Letter) (ps : Vec Letter n) →
        act (w ↑) (σ , p ∷ ps) ≡ (proj₁ (act w (σ , ps)) , p ∷ proj₂ (act w (σ , ps)))
act-↑ [ g ]ʷ  σ p ps = Eq.refl
act-↑ ε       σ p ps = Eq.refl
act-↑ (w • v) σ p ps = Eq.trans (Eq.cong (act (w ↑)) (act-↑ v σ p ps))
  (act-↑ w (proj₁ (act v (σ , ps))) p (proj₂ (act v (σ , ps))))

act⁻-↑ : (w : Circuit n) (σ : Ph) (p : Letter) (ps : Vec Letter n) →
         act⁻ (w ↑) (σ , p ∷ ps) ≡ (proj₁ (act⁻ w (σ , ps)) , p ∷ proj₂ (act⁻ w (σ , ps)))
act⁻-↑ [ g ]ʷ  σ p ps = Eq.refl
act⁻-↑ ε       σ p ps = Eq.refl
act⁻-↑ (w • v) σ p ps = Eq.trans (Eq.cong (act⁻ (v ↑)) (act⁻-↑ w σ p ps))
  (act⁻-↑ v (proj₁ (act⁻ w (σ , ps))) p (proj₂ (act⁻ w (σ , ps))))

-- The identity operator is fixed by every circuit.
I^ : (n : ℕ) → Vec Letter n
I^ n = replicate n 𝐈

actL⁻-I : (g : Gen n) (σ : Ph) → actL⁻ g (σ , I^ n) ≡ (σ , I^ n)
actL⁻-I (gate₀ ω-gate)  σ = Eq.refl
actL⁻-I (gate₁ H-gate)  σ = Eq.refl
actL⁻-I (gate₁ S-gate)  σ = Eq.refl
actL⁻-I (gate₂ CZ-gate) σ = Eq.refl
actL⁻-I {suc n} (g ↥) σ =
  Eq.cong₂ (λ x y → x , 𝐈 ∷ y) (Eq.cong proj₁ (actL⁻-I g σ)) (Eq.cong proj₂ (actL⁻-I g σ))

act⁻-I : (w : Circuit n) (σ : Ph) → act⁻ w (σ , I^ n) ≡ (σ , I^ n)
act⁻-I [ g ]ʷ  σ = actL⁻-I g σ
act⁻-I ε       σ = Eq.refl
act⁻-I (w • v) σ = Eq.trans (Eq.cong (act⁻ v) (act⁻-I w σ)) (act⁻-I v σ)
