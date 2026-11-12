------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of the circuits over X, CX, CCX and Ex: functions on
-- bit vectors
--
-- A circuit on n wires denotes a function on bit vectors of length n,
-- the bit of wire 0 first, read in diagram order: ⟦ w • v ⟧ applies
-- ⟦ w ⟧ first.  Functions are compared pointwise (_≐_), and on a fixed
-- width the comparison is decided by running over all 2ⁿ vectors (eqF,
-- eqF-sound).  Every rule of the theory is sound (sound).  The rules of
-- Syntactics live on four wires and are decided there on the sixteen
-- states; those with indices, Lafont's relations between the cycles
-- Ω i, are decided for all their indices at once, by one boolean that
-- runs over the indices within the bounds.  The laws of the swap and
-- the structural rules hold at every width, by computation on the
-- first bits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Semantics where

open import Data.Bool.Base
  using (Bool ; true ; false ; not ; _∧_ ; _xor_ ; T)
open import Data.Nat.Base
  using (ℕ ; zero ; suc ; _+_ ; _≤_ ; z≤n ; s≤s ; _≤ᵇ_)
open import Data.Nat.Properties using (≤⇒≤ᵇ ; ≤-trans)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Function.Base using (id ; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl)

open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Examples.Groups.Alt16-RevCir.Syntactics

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

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = refl

  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true} h = h

  -- Every vector satisfies p, checked on all 2ⁿ of them.
  allB : (n : ℕ) → (Bits n → Bool) → Bool
  allB zero    p = p []
  allB (suc n) p = allB n (p ∘ (false ∷_)) ∧ allB n (p ∘ (true ∷_))

  allB-sound : (n : ℕ) (p : Bits n → Bool) → allB n p ≡ true →
               ∀ x → p x ≡ true
  allB-sound zero    p h []          = h
  allB-sound (suc n) p h (false ∷ x) = allB-sound n _ (∧-l h) x
  allB-sound (suc n) p h (true ∷ x)  =
    allB-sound n _ (∧-r {allB n (p ∘ (false ∷_))} h) x

  eqB : Bool → Bool → Bool
  eqB true  true  = true
  eqB false false = true
  eqB _     _     = false

  eqV : Bits n → Bits n → Bool
  eqV []      []      = true
  eqV (a ∷ x) (b ∷ y) = eqB a b ∧ eqV x y

  eqV-sound : (x y : Bits n) → eqV x y ≡ true → x ≡ y
  eqV-sound []          []          _ = refl
  eqV-sound (true ∷ x)  (true ∷ y)  h =
    Eq.cong (true ∷_) (eqV-sound x y h)
  eqV-sound (false ∷ x) (false ∷ y) h =
    Eq.cong (false ∷_) (eqV-sound x y h)

eqF : (n : ℕ) → Fun n → Fun n → Bool
eqF n f g = allB n (λ x → eqV (f x) (g x))

eqF-sound : (n : ℕ) (f g : Fun n) → eqF n f g ≡ true → f ≐ g
eqF-sound n f g h x = eqV-sound (f x) (g x) (allB-sound n _ h x)

------------------------------------------------------------------------
-- The gates

⟦_⟧ᵍ : Gen n → Fun n
⟦ gate₀ () ⟧ᵍ
⟦ X-gen    ⟧ᵍ (a ∷ x)         = not a ∷ x
⟦ CX-gen   ⟧ᵍ (a ∷ b ∷ x)     = (a xor b) ∷ b ∷ x
⟦ Ex-gen   ⟧ᵍ (a ∷ b ∷ x)     = b ∷ a ∷ x
⟦ CCX-gen  ⟧ᵍ (a ∷ b ∷ c ∷ x) = (a xor (b ∧ c)) ∷ b ∷ c ∷ x
⟦ g ↥      ⟧ᵍ                 = up ⟦ g ⟧ᵍ

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
  Eq.trans (⟦↑⟧ v (⟦ w ↑ ⟧ (a ∷ x)))
           (Eq.cong (up ⟦ v ⟧) (⟦↑⟧ w (a ∷ x)))

------------------------------------------------------------------------
-- Deciding a rule for all its indices

private
  -- Every i ≤ n satisfies p.
  all≤ : ℕ → (ℕ → Bool) → Bool
  all≤ zero    p = p 0
  all≤ (suc n) p = p 0 ∧ all≤ n (p ∘ suc)

  all≤-sound : ∀ n p → all≤ n p ≡ true → ∀ i → i ≤ n → p i ≡ true
  all≤-sound zero    p h zero    z≤n     = h
  all≤-sound (suc n) p h zero    z≤n     = ∧-l h
  all≤-sound (suc n) p h (suc i) (s≤s l) =
    all≤-sound n _ (∧-r {p 0} h) i l

  -- A condition under a guard.
  infixr 3 _⇒_
  _⇒_ : Bool → Bool → Bool
  true  ⇒ b = b
  false ⇒ _ = true

  ⇒-sound : ∀ {a b} → T a → (a ⇒ b) ≡ true → b ≡ true
  ⇒-sound {true} _ h = h

  drop3 : ∀ {i m} → 3 + i ≤ 3 + m → i ≤ m
  drop3 (s≤s (s≤s (s≤s l))) = l

------------------------------------------------------------------------
-- Soundness

private
  -- The rules of Syntactics, on the sixteen states.  The two sides of
  -- Lafont's relations at position i, and of the commutation of the
  -- cycles at i and j, are named so that the boolean decided and the
  -- one used are the same term.
  orderᵇ nearᵇ farᵇ : ℕ → Bool
  orderᵇ i = same 4 (Ω i • Ω i • Ω i) ε
  nearᵇ  i = same 4 (Ω i • Ω (1 + i) • Ω i) (Ω (1 + i) • Ω (1 + i))
  farᵇ   i =
    same 4 (Ω i • Ω (2 + i) • Ω i) (Ω (2 + i) • Ω i • Ω (1 + i))

  apartᵇ : ℕ → ℕ → Bool
  apartᵇ i j = 3 + i ≤ᵇ j ⇒ same 4 (Ω j • Ω i) (Ω i • Ω j)

  srel-sound : ∀ {w v : Circuit n} → n SRel, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
  srel-sound {w = w} {v} (order i l) =
    same-sound w v (all≤-sound 13 orderᵇ refl i l)
  srel-sound {w = w} {v} (near i l) =
    same-sound w v (all≤-sound 12 nearᵇ refl i l)
  srel-sound {w = w} {v} (far i l) =
    same-sound w v (all≤-sound 11 farᵇ refl i l)
  srel-sound {w = w} {v} (apart i j l l′) =
    same-sound w v (⇒-sound (≤⇒≤ᵇ l)
      (all≤-sound 13 (apartᵇ i)
        (all≤-sound 10 (λ i → all≤ 13 (apartᵇ i)) refl i
          (drop3 (≤-trans l l′)))
        j l′))
  srel-sound {w = w} {v} gate-X   = same-sound w v refl
  srel-sound {w = w} {v} gate-CX  = same-sound w v refl
  srel-sound {w = w} {v} gate-CCX = same-sound w v refl
  srel-sound {w = w} {v} gate-Ex₀ = same-sound w v refl
  srel-sound {w = w} {v} gate-Ex₁ = same-sound w v refl
  srel-sound {w = w} {v} gate-Ex₂ = same-sound w v refl

  -- The laws of the swap, at every width.
  sym-sound : ∀ {w v : Circuit n} → n Sym, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
  sym-sound σ-inv              (a ∷ b ∷ x)         = refl
  sym-sound (σ-nat₁ X-gate)    (a ∷ b ∷ x)         = refl
  sym-sound (σ-nat₂ CX-gate)   (a ∷ b ∷ c ∷ x)     = refl
  sym-sound (σ-nat₂ Ex-gate)   (a ∷ b ∷ c ∷ x)     = refl
  sym-sound (σ-nat₃ CCX-gate)  (a ∷ b ∷ c ∷ d ∷ x) = refl

-- Every rule: those of Syntactics, the laws of the swap and the
-- structural rules.
ax-sound : ∀ {w v : Circuit n} → n VRel, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
ax-sound (srel (srel r)) = srel-sound r
ax-sound (srel (σrel s)) = sym-sound s
ax-sound (cong↑ {w = w} {v = v} a) =
  ≐-trans (⟦↑⟧ w) (≐-trans (up-cong (ax-sound a)) (≐-sym (⟦↑⟧ v)))
ax-sound (comm₁ X-gate g)   (a ∷ x)         = refl
ax-sound (comm₂ CX-gate g)  (a ∷ b ∷ x)     = refl
ax-sound (comm₂ Ex-gate g)  (a ∷ b ∷ x)     = refl
ax-sound (comm₃ CCX-gate g) (a ∷ b ∷ c ∷ x) = refl
ax-sound (ω↑=ω ())

-- The theory is sound.
sound : {w v : Circuit n} → n ⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
sound PB.refl         = ≐-refl
sound (PB.sym e)      = ≐-sym (sound e)
sound (PB.trans e e′) = ≐-trans (sound e) (sound e′)
sound (PB.cong e e′)  = ⨾-cong (sound e) (sound e′)
sound PB.assoc        = ≐-refl
sound PB.left-unit    = ≐-refl
sound PB.right-unit   = ≐-refl
sound (PB.axiom a)    = ax-sound a
