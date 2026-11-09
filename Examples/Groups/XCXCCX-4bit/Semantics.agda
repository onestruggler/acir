------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of {X, CX, CCX} circuits: permutations of bit vectors
--
-- A circuit on n wires denotes a function on bit vectors of length n,
-- wire 0 first, read in diagram order: ⟦ w • v ⟧ applies ⟦ w ⟧ first.
-- Functions are compared pointwise (_≐_), and on a fixed width the
-- comparison is decided by running over all 2ⁿ vectors (eqF, eqF-sound).
-- Every relation of the theory, and every swap and structural rule, is
-- sound (sound): the seven rules by evaluation at the width they are
-- drawn on, the rest at every width by computation on the first bits.
--
-- A state of the paper, x₁x₂…xₙ with x₁ the most significant bit, is
-- the vector whose entry on wire w is x_{n−w}: the paper's wire 1 is our
-- top wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.XCXCCX-4bit.Semantics where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Function.Base using (id ; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.XCXCCX-4bit.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Functions on bit vectors

Bits : ℕ → Set
Bits n = Vec Bool n

Fun : ℕ → Set
Fun n = Bits n → Bits n

infix 4 _≐_
_≐_ : Fun n → Fun n → Set
f ≐ g = ∀ x → f x ≡ g x

≐-refl : {f : Fun n} → f ≐ f
≐-refl x = refl

≐-sym : {f g : Fun n} → f ≐ g → g ≐ f
≐-sym e x = Eq.sym (e x)

≐-trans : {f g h : Fun n} → f ≐ g → g ≐ h → f ≐ h
≐-trans e e′ x = Eq.trans (e x) (e′ x)

-- Composition in diagram order: f first, then g.
infixr 9 _⨾_
_⨾_ : Fun n → Fun n → Fun n
(f ⨾ g) x = g (f x)

⨾-cong : {f f′ g g′ : Fun n} → f ≐ f′ → g ≐ g′ → (f ⨾ g) ≐ (f′ ⨾ g′)
⨾-cong {f′ = f′} {g} e e′ x = Eq.trans (Eq.cong g (e x)) (e′ (f′ x))

-- A function on the wires above the bottom one.
up : Fun n → Fun (suc n)
up f (a ∷ x) = a ∷ f x

up-cong : {f g : Fun n} → f ≐ g → up f ≐ up g
up-cong e (a ∷ x) = Eq.cong (a ∷_) (e x)

------------------------------------------------------------------------
-- Deciding pointwise equality

-- Every vector satisfies p, checked on all 2ⁿ of them.
allB : (n : ℕ) → (Bits n → Bool) → Bool
allB zero    p = p []
allB (suc n) p = allB n (λ x → p (false ∷ x)) ∧ allB n (λ x → p (true ∷ x))

∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-l {true} _ = refl

∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
∧-r {true} h = h

allB-sound : (n : ℕ) (p : Bits n → Bool) → allB n p ≡ true → ∀ x → p x ≡ true
allB-sound zero    p h []          = h
allB-sound (suc n) p h (false ∷ x) = allB-sound n _ (∧-l h) x
allB-sound (suc n) p h (true ∷ x)  = allB-sound n _ (∧-r {allB n (λ x → p (false ∷ x))} h) x

eqB : Bool → Bool → Bool
eqB true  true  = true
eqB false false = true
eqB _     _     = false

eqB-sound : (a b : Bool) → eqB a b ≡ true → a ≡ b
eqB-sound true  true  _ = refl
eqB-sound false false _ = refl

eqV : Bits n → Bits n → Bool
eqV []       []       = true
eqV (a ∷ x)  (b ∷ y)  = eqB a b ∧ eqV x y

eqV-sound : (x y : Bits n) → eqV x y ≡ true → x ≡ y
eqV-sound []      []      _ = refl
eqV-sound (a ∷ x) (b ∷ y) h with eqB a b in e
eqV-sound (a ∷ x) (b ∷ y) h  | true  = Eq.cong₂ _∷_ (eqB-sound a b e) (eqV-sound x y h)
eqV-sound (a ∷ x) (b ∷ y) () | false

eqF : (n : ℕ) → Fun n → Fun n → Bool
eqF n f g = allB n (λ x → eqV (f x) (g x))

eqF-sound : (n : ℕ) (f g : Fun n) → eqF n f g ≡ true → f ≐ g
eqF-sound n f g h x = eqV-sound (f x) (g x) (allB-sound n _ h x)

------------------------------------------------------------------------
-- The gates

⟦_⟧ᵍ : Gen n → Fun n
⟦ gate₀ ⌈ () ⌉     ⟧ᵍ
⟦ gate₁ ⌈ X-gate ⌉ ⟧ᵍ (a ∷ x)         = not a ∷ x
⟦ gate₂ ⌈ CX-gate ⌉ ⟧ᵍ (a ∷ b ∷ x)    = (a xor b) ∷ b ∷ x
⟦ gate₂ swap ⟧ᵍ (a ∷ b ∷ x)           = b ∷ a ∷ x
⟦ gate₃ ⌈ CCX-gate ⌉ ⟧ᵍ (a ∷ b ∷ c ∷ x) = (a xor (b ∧ c)) ∷ b ∷ c ∷ x
⟦ g ↥ ⟧ᵍ                              = up ⟦ g ⟧ᵍ

-- A word, its letters in diagram order.
⟦_⟧ : Circuit n → Fun n
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ ε ⟧      = id
⟦ w • v ⟧  = ⟦ w ⟧ ⨾ ⟦ v ⟧

-- Two circuits on n wires with the same function, decided.
same : (n : ℕ) → Circuit n → Circuit n → Bool
same n w v = eqF n ⟦ w ⟧ ⟦ v ⟧

same-sound : (w v : Circuit n) → same n w v ≡ true → ⟦ w ⟧ ≐ ⟦ v ⟧
same-sound {n} w v = eqF-sound n ⟦ w ⟧ ⟦ v ⟧

------------------------------------------------------------------------
-- Shifting

⟦↑⟧ : (w : Circuit n) → ⟦ w ↑ ⟧ ≐ up ⟦ w ⟧
⟦↑⟧ [ g ]ʷ  x       = refl
⟦↑⟧ ε       (a ∷ x) = refl
⟦↑⟧ (w • v) (a ∷ x) =
  Eq.trans (⟦↑⟧ v (⟦ w ↑ ⟧ (a ∷ x))) (Eq.cong (up ⟦ v ⟧) (⟦↑⟧ w (a ∷ x)))

------------------------------------------------------------------------
-- Soundness

private
  -- The seven rules, at the widths they are drawn on.
  srel-sound : ∀ {w v : Circuit n} → n SRel, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
  srel-sound {w = w} {v} r1 = same-sound w v refl
  srel-sound {w = w} {v} r2 = same-sound w v refl
  srel-sound {w = w} {v} r3 = same-sound w v refl
  srel-sound {w = w} {v} r4 = same-sound w v refl
  srel-sound {w = w} {v} r5 = same-sound w v refl
  srel-sound {w = w} {v} r6 = same-sound w v refl
  srel-sound {w = w} {v} r7 = same-sound w v refl

  -- The swap rules, at every width.
  sym-sound : ∀ {w v : Circuit n} → n Sym, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
  sym-sound σ-inv                     (a ∷ b ∷ x)         = refl
  sym-sound (σ-nat₁ ⌈ X-gate ⌉)       (a ∷ b ∷ x)         = refl
  sym-sound (σ-nat₂ ⌈ CX-gate ⌉)      (a ∷ b ∷ c ∷ x)     = refl
  sym-sound (σ-nat₂ swap)             (a ∷ b ∷ c ∷ x)     = refl
  sym-sound (σ-nat₃ ⌈ CCX-gate ⌉)     (a ∷ b ∷ c ∷ d ∷ x) = refl

  -- The structural rules.
  ax-sound : ∀ {w v : Circuit n} → n VRel, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
  ax-sound (srel (srel r))  = srel-sound r
  ax-sound (srel (σrel s))  = sym-sound s
  ax-sound (cong↑ {w = w} {v = v} a) =
    ≐-trans (⟦↑⟧ w) (≐-trans (up-cong (ax-sound a)) (≐-sym (⟦↑⟧ v)))
  ax-sound (comm₁ ⌈ X-gate ⌉ g)    (a ∷ x)         = refl
  ax-sound (comm₂ ⌈ CX-gate ⌉ g)   (a ∷ b ∷ x)     = refl
  ax-sound (comm₂ swap g)          (a ∷ b ∷ x)     = refl
  ax-sound (comm₃ ⌈ CCX-gate ⌉ g)  (a ∷ b ∷ c ∷ x) = refl
  ax-sound (ω↑=ω ⌈ () ⌉)

-- The theory, with the swap and structural rules, is sound.
sound : {w v : Circuit n} → n ⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
sound PB.refl           = ≐-refl
sound (PB.sym e)        = ≐-sym (sound e)
sound (PB.trans e e′)   = ≐-trans (sound e) (sound e′)
sound (PB.cong e e′)    = ⨾-cong (sound e) (sound e′)
sound PB.assoc          = ≐-refl
sound PB.left-unit      = ≐-refl
sound PB.right-unit     = ≐-refl
sound (PB.axiom a)      = ax-sound a
