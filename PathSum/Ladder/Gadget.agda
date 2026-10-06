------------------------------------------------------------------------
-- Presentations of groups
--
-- The Boolean bookkeeping of a ladder of Toffoli gadgets (for Amy,
-- QPL 2018, proposition 3.2)
--
-- PathSum.Ladder writes down a family of path-sums ξ n, a ladder of n
-- Toffoli gadgets, and PathSum.Ladder.Invariant describes every
-- path-sum figure 2 can reach from it.  What such a path-sum computes
-- is read off this module's formulas, which are pure Boolean
-- functions: no polynomial, no precision.
--
-- Gadget g has an input bit x_g, a target bit a_g and two path
-- variables, u_g (internal) and v_g (on the output wire of a_g).  It
-- is in one of three states.  Live: neither variable has been removed
-- yet; it contributes u_g (v_g ⊕ c_g) to the phase (read as
-- ½·(that bit)) and v_g to its output, where
--
--    c_g = a_g ⊕ (¬x_g ∧ V_(g-1))      (gval)
--
-- and V_(g-1) is the value the previous gadget hands on (V_(-1) = 1).
-- Half: [HH] at u_g has substituted c_g for v_g, which is left as a
-- variable no polynomial mentions; the gadget contributes nothing to
-- the phase and c_g to its output.  Dead: [Elim] has removed v_g too;
-- the same contribution.  The value handed on is v_g if the gadget is
-- live and c_g otherwise (step); prevAt reads the value reaching a
-- gadget, Vs the value it hands on (its output), Bsum the phase bit
-- (the exclusive or of the contributions).
--
-- The lemma everything rests on is one-change: two environments that
-- agree, contribution for contribution, except at one gadget g, which
-- hands on the same value in both, have the same outputs, and phases
-- that differ by the change of g's contribution.  Its instances are
-- the rule steps of PathSum.Ladder.Steps (live to half, half to dead,
-- a variable flipped).  Also here: the normalisation each state
-- carries (weight, wsum: 2 for live and half, 0 for dead), the values
-- of an all-live ladder (prevAt-live) and of an all-dead one with its
-- targets 0 (Vs-dead: the NOR of the inputs).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Ladder.Gadget where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-assoc)
open import Data.Fin.Base using (Fin; zero; suc; inject₁; fromℕ)
open import Data.Fin.Properties using (suc-injective)
  renaming (_≟_ to _≟ᶠ_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Product.Properties as Product

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- States, kinds of path variables, gadgets

data State : Set where
  live half dead : State

data Kind : Set where
  U V : Kind

_≟ᵏ_ : DecidableEquality Kind
U ≟ᵏ U = yes refl
U ≟ᵏ V = no λ ()
V ≟ᵏ U = no λ ()
V ≟ᵏ V = yes refl

-- The role of a path variable: its gadget and its kind.

Role : ℕ → Set
Role n = Fin n × Kind

_≟ʳ_ : DecidableEquality (Role n)
_≟ʳ_ = Product.≡-dec _≟ᶠ_ _≟ᵏ_

-- Which path variables a gadget in each state still has.

present : State → Kind → Bool
present live _ = true
present half U = false
present half V = true
present dead _ = false

-- The normalisation each state carries: 1/2 for the pair u_g, v_g of a
-- live gadget, still 1/2 after [HH] (the path-sum keeps its
-- normalisation), nothing after [Elim].

weight : State → ℕ
weight live = 2
weight half = 2
weight dead = 0

-- A gadget's data at one Boolean point: its state, x_g, a_g, u_g, v_g.

record Gad : Set where
  constructor gad
  field
    state : State
    xb ab ub vb : Bool

open Gad public


------------------------------------------------------------------------
-- What a gadget contributes

-- c_g = a_g ⊕ (¬x_g ∧ V_(g-1)).

gval : Gad → Bool → Bool
gval G p = ab G xor (not (xb G) ∧ p)

stepˢ : State → Bool → Bool → Bool
stepˢ live v c = v
stepˢ half v c = c
stepˢ dead v c = c

termˢ : State → Bool → Bool → Bool → Bool
termˢ live u v c = u ∧ (v xor c)
termˢ half u v c = false
termˢ dead u v c = false

-- The value handed on, and the contribution to the phase bit, given
-- the value p reaching the gadget.

step : Gad → Bool → Bool
step G p = stepˢ (state G) (vb G) (gval G p)

term : Gad → Bool → Bool
term G p = termˢ (state G) (ub G) (vb G) (gval G p)

-- The same, read through the state.

step-live : ∀ G p → state G ≡ live → step G p ≡ vb G
step-live G p e = cong (λ s → stepˢ s (vb G) (gval G p)) e

step-half : ∀ G p → state G ≡ half → step G p ≡ gval G p
step-half G p e = cong (λ s → stepˢ s (vb G) (gval G p)) e

step-dead : ∀ G p → state G ≡ dead → step G p ≡ gval G p
step-dead G p e = cong (λ s → stepˢ s (vb G) (gval G p)) e

term-live : ∀ G p → state G ≡ live →
            term G p ≡ ub G ∧ (vb G xor gval G p)
term-live G p e = cong (λ s → termˢ s (ub G) (vb G) (gval G p)) e

term-half : ∀ G p → state G ≡ half → term G p ≡ false
term-half G p e = cong (λ s → termˢ s (ub G) (vb G) (gval G p)) e

term-dead : ∀ G p → state G ≡ dead → term G p ≡ false
term-dead G p e = cong (λ s → termˢ s (ub G) (vb G) (gval G p)) e


------------------------------------------------------------------------
-- A ladder

-- The value reaching gadget g, the value it hands on, and the phase
-- bit, for gadgets 0, 1, ..., n - 1 in order, the value p reaching
-- gadget 0.

prevAt : Bool → (Fin n → Gad) → Fin n → Bool
prevAt p G zero    = p
prevAt p G (suc g) = prevAt (step (G zero) p) (λ h → G (suc h)) g

Vs : Bool → (Fin n → Gad) → Fin n → Bool
Vs p G g = step (G g) (prevAt p G g)

Bsum : Bool → (Fin n → Gad) → Bool
Bsum {zero}  p G = false
Bsum {suc n} p G =
  term (G zero) p xor Bsum (step (G zero) p) (λ h → G (suc h))


------------------------------------------------------------------------
-- Congruence

-- Environments that take the same steps reach the same values ...

prevAt-cong : (G G′ : Fin n → Gad) →
              (∀ h q → step (G h) q ≡ step (G′ h) q) →
              ∀ p g → prevAt p G g ≡ prevAt p G′ g
prevAt-cong G G′ hs p zero    = refl
prevAt-cong G G′ hs p (suc g) = trans
  (cong (λ q → prevAt q (λ h → G (suc h)) g) (hs zero p))
  (prevAt-cong (λ h → G (suc h)) (λ h → G′ (suc h)) (λ h → hs (suc h))
               (step (G′ zero) p) g)

Vs-cong : (G G′ : Fin n → Gad) →
          (∀ h q → step (G h) q ≡ step (G′ h) q) →
          ∀ p g → Vs p G g ≡ Vs p G′ g
Vs-cong G G′ hs p g =
  trans (cong (step (G g)) (prevAt-cong G G′ hs p g))
        (hs g (prevAt p G′ g))

-- ... and, contributing the same, the same phase bit.

Bsum-cong : (G G′ : Fin n → Gad) →
            (∀ h q → step (G h) q ≡ step (G′ h) q) →
            (∀ h q → term (G h) q ≡ term (G′ h) q) →
            ∀ p → Bsum p G ≡ Bsum p G′
Bsum-cong {zero}  G G′ hs ht p = refl
Bsum-cong {suc n} G G′ hs ht p = cong₂ _xor_ (ht zero p)
  (trans (cong (λ q → Bsum q (λ h → G (suc h))) (hs zero p))
         (Bsum-cong (λ h → G (suc h)) (λ h → G′ (suc h))
                    (λ h → hs (suc h)) (λ h → ht (suc h))
                    (step (G′ zero) p)))


------------------------------------------------------------------------
-- One gadget changes

private
  xor-shuffle : ∀ t t′ r → t xor r ≡ (t′ xor r) xor (t xor t′)
  xor-shuffle true  true  true  = refl
  xor-shuffle true  true  false = refl
  xor-shuffle true  false true  = refl
  xor-shuffle true  false false = refl
  xor-shuffle false true  true  = refl
  xor-shuffle false true  false = refl
  xor-shuffle false false true  = refl
  xor-shuffle false false false = refl

  suc≢zero : ∀ {h : Fin n} → suc h ≢ zero
  suc≢zero ()

  zero≢suc : ∀ {h : Fin n} → zero ≢ suc h
  zero≢suc ()

-- Two environments agreeing off g, step for step and contribution for
-- contribution, whose gadget g hands on the same value: the same
-- outputs, and phase bits differing by the change of g's contribution.

one-change : (G G′ : Fin n → Gad) (g : Fin n) (p : Bool) →
             (∀ h → h ≢ g → ∀ q → step (G h) q ≡ step (G′ h) q) →
             (∀ h → h ≢ g → ∀ q → term (G h) q ≡ term (G′ h) q) →
             step (G g) (prevAt p G g) ≡ step (G′ g) (prevAt p G g) →
             (Bsum p G ≡
              Bsum p G′ xor (term (G g) (prevAt p G g) xor
                             term (G′ g) (prevAt p G g))) ×
             (∀ h → Vs p G h ≡ Vs p G′ h)
one-change {suc n} G G′ zero p hs ht hg = bsum , vs
  where
  rest : Bsum (step (G zero) p) (λ h → G (suc h)) ≡
         Bsum (step (G′ zero) p) (λ h → G′ (suc h))
  rest = trans (cong (λ q → Bsum q (λ h → G (suc h))) hg)
    (Bsum-cong (λ h → G (suc h)) (λ h → G′ (suc h))
               (λ h → hs (suc h) suc≢zero) (λ h → ht (suc h) suc≢zero)
               (step (G′ zero) p))

  bsum : Bsum p G ≡ Bsum p G′ xor (term (G zero) p xor term (G′ zero) p)
  bsum = trans (cong (term (G zero) p xor_) rest)
    (xor-shuffle (term (G zero) p) (term (G′ zero) p)
                 (Bsum (step (G′ zero) p) (λ h → G′ (suc h))))

  vs : ∀ h → Vs p G h ≡ Vs p G′ h
  vs zero    = hg
  vs (suc h) = trans
    (cong (λ q → Vs q (λ l → G (suc l)) h) hg)
    (Vs-cong (λ l → G (suc l)) (λ l → G′ (suc l))
             (λ l → hs (suc l) suc≢zero) (step (G′ zero) p) h)
one-change {suc n} G G′ (suc g) p hs ht hg = bsum , vs
  where
  p₁ : Bool
  p₁ = step (G zero) p

  s₀ : p₁ ≡ step (G′ zero) p
  s₀ = hs zero zero≢suc p

  ih = one-change (λ h → G (suc h)) (λ h → G′ (suc h)) g p₁
         (λ h h≢g → hs (suc h) (λ e → h≢g (suc-injective e)))
         (λ h h≢g → ht (suc h) (λ e → h≢g (suc-injective e)))
         hg

  Δ : Bool
  Δ = term (G (suc g)) (prevAt p G (suc g)) xor
      term (G′ (suc g)) (prevAt p G (suc g))

  bsum : Bsum p G ≡ Bsum p G′ xor Δ
  bsum = trans (cong (term (G zero) p xor_) (proj₁ ih))
    (trans (sym (xor-assoc (term (G zero) p)
                           (Bsum p₁ (λ h → G′ (suc h))) Δ))
           (cong (_xor Δ)
             (cong₂ _xor_ (ht zero zero≢suc p)
                    (cong (λ q → Bsum q (λ h → G′ (suc h))) s₀))))

  vs : ∀ h → Vs p G h ≡ Vs p G′ h
  vs zero    = s₀
  vs (suc h) = trans (proj₂ ih h)
    (cong (λ q → Vs q (λ l → G′ (suc l)) h) s₀)

-- The value reaching g depends only on the gadgets before it.

prevAt-off : (G G′ : Fin n → Gad) (g : Fin n) (p : Bool) →
             (∀ h → h ≢ g → ∀ q → step (G h) q ≡ step (G′ h) q) →
             prevAt p G g ≡ prevAt p G′ g
prevAt-off {suc n} G G′ zero    p hs = refl
prevAt-off {suc n} G G′ (suc g) p hs = trans
  (cong (λ q → prevAt q (λ h → G (suc h)) g) (hs zero zero≢suc p))
  (prevAt-off (λ h → G (suc h)) (λ h → G′ (suc h)) g
              (step (G′ zero) p)
              (λ h h≢g → hs (suc h) (λ e → h≢g (suc-injective e))))


------------------------------------------------------------------------
-- Ladders all live, and all dead

-- All live: the value reaching gadget g + 1 is v_g.

prevAt-live : (G : Fin (suc n) → Gad) → (∀ h → state (G h) ≡ live) →
              ∀ p (h : Fin n) → prevAt p G (suc h) ≡ vb (G (inject₁ h))
prevAt-live G live? p zero    = step-live (G zero) p (live? zero)
prevAt-live {suc n} G live? p (suc h) =
  prevAt-live (λ l → G (suc l)) (λ l → live? (suc l)) (step (G zero) p) h

-- All dead with every target 0: gadget g hands on p ∧ ¬x_0 ∧ … ∧ ¬x_g,
-- so the last one the NOR of the inputs (when p is true).

andNot : Bool → (Fin n → Bool) → Bool
andNot {zero}  p x = p
andNot {suc n} p x = andNot (not (x zero) ∧ p) (λ i → x (suc i))

Vs-dead : (G : Fin (suc n) → Gad) → (∀ h → state (G h) ≡ dead) →
          (∀ h → ab (G h) ≡ false) →
          ∀ p → Vs p G (fromℕ n) ≡ andNot p (λ h → xb (G h))
Vs-dead {zero}  G dead? ab0 p =
  trans (step-dead (G zero) p (dead? zero))
        (cong (λ a → a xor (not (xb (G zero)) ∧ p)) (ab0 zero))
Vs-dead {suc n} G dead? ab0 p = trans
  (Vs-dead (λ l → G (suc l)) (λ l → dead? (suc l)) (λ l → ab0 (suc l))
           (step (G zero) p))
  (cong (λ q → andNot q (λ h → xb (G (suc h))))
        (trans (step-dead (G zero) p (dead? zero))
               (cong (λ a → a xor (not (xb (G zero)) ∧ p)) (ab0 zero))))


------------------------------------------------------------------------
-- States: updating one, and the normalisation they carry

upd : (Fin n → State) → Fin n → State → Fin n → State
upd s g t h = if ⌊ h ≟ᶠ g ⌋ then t else s h

upd-here : (s : Fin n → State) (g : Fin n) (t : State) → upd s g t g ≡ t
upd-here s g t with g ≟ᶠ g
... | yes _ = refl
... | no ¬p = contradiction refl ¬p

upd-there : (s : Fin n → State) {g h : Fin n} (t : State) → h ≢ g →
            upd s g t h ≡ s h
upd-there s {g} {h} t h≢g with h ≟ᶠ g
... | yes e = contradiction e h≢g
... | no  _ = refl

wsum : (Fin n → State) → ℕ
wsum {zero}  s = 0
wsum {suc n} s = weight (s zero) + wsum (λ h → s (suc h))

wsum-cong : {s s′ : Fin n → State} → (∀ h → s h ≡ s′ h) →
            wsum s ≡ wsum s′
wsum-cong {zero}  h = refl
wsum-cong {suc n} h =
  cong₂ _+_ (cong weight (h zero)) (wsum-cong (λ l → h (suc l)))

private
  upd-suc : (s : Fin (suc n) → State) (g h : Fin n) (t : State) →
            upd s (suc g) t (suc h) ≡ upd (λ l → s (suc l)) g t h
  upd-suc s g h t = by (h ≟ᶠ g)
    where
    s′ : Fin _ → State
    s′ l = s (suc l)

    by : Dec (h ≡ g) → upd s (suc g) t (suc h) ≡ upd s′ g t h
    by (yes h≡g) = trans (cong (λ l → upd s (suc g) t (suc l)) h≡g)
      (trans (upd-here s (suc g) t)
             (sym (trans (cong (upd s′ g t) h≡g) (upd-here s′ g t))))
    by (no h≢g) = trans (upd-there s t (λ e → h≢g (suc-injective e)))
                        (sym (upd-there s′ t h≢g))

  swap-middle : ∀ a b c → a + (b + c) ≡ b + (a + c)
  swap-middle a b c = trans (sym (+-assoc a b c))
    (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

-- The weight of g split off.

wsum-split : (s : Fin n → State) (g : Fin n) →
             wsum s ≡ weight (s g) + wsum (upd s g dead)
wsum-split {suc n} s zero = cong (weight (s zero) +_)
  (wsum-cong {s = λ h → s (suc h)} {s′ = λ h → upd s zero dead (suc h)}
             (λ h → sym (upd-there s dead suc≢zero)))
wsum-split {suc n} s (suc g) = trans
  (cong (weight (s zero) +_) (wsum-split (λ h → s (suc h)) g))
  (trans (swap-middle (weight (s zero)) (weight (s (suc g)))
                      (wsum (upd (λ h → s (suc h)) g dead)))
         (cong (weight (s (suc g)) +_)
               (cong (weight (s zero) +_)
                 (wsum-cong {s = upd (λ h → s (suc h)) g dead}
                            {s′ = λ h → upd s (suc g) dead (suc h)}
                            (λ h → sym (upd-suc s g h dead))))))

-- Updating g to t.

wsum-upd : (s : Fin n → State) (g : Fin n) (t : State) →
           wsum (upd s g t) ≡ weight t + wsum (upd s g dead)
wsum-upd s g t = trans (wsum-split (upd s g t) g)
  (cong₂ _+_ (cong weight (upd-here s g t)) (wsum-cong same))
  where
  same : ∀ h → upd (upd s g t) g dead h ≡ upd s g dead h
  same h = by (h ≟ᶠ g)
    where
    by : Dec (h ≡ g) → upd (upd s g t) g dead h ≡ upd s g dead h
    by (yes h≡g) = trans (cong (upd (upd s g t) g dead) h≡g)
      (trans (upd-here (upd s g t) g dead)
             (sym (trans (cong (upd s g dead) h≡g) (upd-here s g dead))))
    by (no h≢g) = trans (upd-there (upd s g t) dead h≢g)
      (trans (upd-there s t h≢g) (sym (upd-there s dead h≢g)))
