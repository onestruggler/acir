------------------------------------------------------------------------
-- Presentations of groups
--
-- Bit maps: what the words of Equations (36) and (37) do to basis
-- vectors
--
-- The words `Encoding.W₁`/`W₂` are Hadamard-free around the standard
-- pair, and on basis vectors each of their halves is a composite of
-- exchanges of adjacent wires and flips of single wires.  This module
-- has those actions on bitstrings, at any width: the exchange
-- (`swapBits`) and the conditional flip (`cflip`), their composites
-- along a list (`run`), that a composite is undone by the reverse
-- composite of the inverses (`tele`), what the swap network does — it
-- carries wires i < j to wires 0 and 1, the other wires keeping their
-- order (`network`) — and that the negations then clear the controls
-- (`negs`).  And the facts about `diff` that read Figure 8's H-pattern
-- back: four codes with it are a, a with one bit flipped, a with
-- another, and a with both (`hpat-inv`, `Flips`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.BitAlg where

open import Data.Bool using (Bool ; true ; false ; _xor_ ; not ; _∧_ ; _∨_ ; if_then_else_ ; T)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; map ; reverse ; applyUpTo ; upTo ; _++_ ; _∷ʳ_)
open import Data.List.Properties using (unfold-reverse ; reverse-++)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.List.Relation.Unary.All.Properties using (map⁺ ; applyUpTo⁺₁ ; ∷ʳ⁺)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _≤_ ; _<_ ; z≤n ; s≤s ; _≡ᵇ_ ; _<?_)
open import Data.Nat.Properties
  using (≡ᵇ⇒≡ ; m<n⇒m<1+n ; n<1+n ; +-suc ; +-identityʳ ; m≤m+n ; ≮⇒≥ ; ≤-refl
       ; +-∸-assoc ; m+[n∸m]≡n ; n∸n≡0 ; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
open import Examples.Groups.Real-Clifford+CH.Encoding using (hpat ; range↑ ; range↓)

open Eq.≡-Reasoning

private
  variable
    n k : ℕ

  -- Boolean facts, by cases.
  xor-f : ∀ x → x xor false ≡ x
  xor-f true  = Eq.refl
  xor-f false = Eq.refl

  t-xor : ∀ x → true xor x ≡ x xor true
  t-xor true  = Eq.refl
  t-xor false = Eq.refl

  tt-xor : ∀ x → true xor (true xor x) ≡ x
  tt-xor true  = Eq.refl
  tt-xor false = Eq.refl

  ∨-f : ∀ x → x ∨ false ≡ x
  ∨-f true  = Eq.refl
  ∨-f false = Eq.refl

  ∧-l : ∀ x y → x ∧ y ≡ true → x ≡ true
  ∧-l true  y _ = Eq.refl
  ∧-l false y ()

  ∧-r : ∀ x y → x ∧ y ≡ true → y ≡ true
  ∧-r true  y e = e
  ∧-r false y ()

  not-t : ∀ x → not x ≡ true → x ≡ false
  not-t false _ = Eq.refl
  not-t true  ()

  ≡ᵇ-refl : ∀ i → (i ≡ᵇ i) ≡ true
  ≡ᵇ-refl zero    = Eq.refl
  ≡ᵇ-refl (suc i) = ≡ᵇ-refl i

  ≡ᵇ-< : ∀ w i → w < i → (w ≡ᵇ i) ≡ false
  ≡ᵇ-< zero    (suc i) _       = Eq.refl
  ≡ᵇ-< (suc w) (suc i) (s≤s p) = ≡ᵇ-< w i p

  ≡ᵇ-suc+ : ∀ i w → (suc (i + w) ≡ᵇ i) ≡ false
  ≡ᵇ-suc+ zero    w = Eq.refl
  ≡ᵇ-suc+ (suc i) w = ≡ᵇ-suc+ i w

  ≡ᵇ-true : ∀ x y → (x ≡ᵇ y) ≡ true → x ≡ y
  ≡ᵇ-true x y e = ≡ᵇ⇒≡ x y (Eq.subst T (Eq.sym e) tt)

  ≡ᵇ-false : ∀ x y → x ≢ y → (x ≡ᵇ y) ≡ false
  ≡ᵇ-false x y ne with x ≡ᵇ y in e
  ... | true  = ⊥-elim (ne (≡ᵇ-true x y e))
  ... | false = Eq.refl

------------------------------------------------------------------------
-- Bitstrings are determined by their bits

vec-ext : ∀ (x y : Bits n) → (∀ w → lookupℕ w x ≡ lookupℕ w y) → x ≡ y
vec-ext []      []      _ = Eq.refl
vec-ext (a ∷ x) (b ∷ y) h = Eq.cong₂ _∷_ (h 0) (vec-ext x y (λ w → h (suc w)))

-- There are none above the top wire.
lookup-beyond : ∀ w (x : Bits n) → n ≤ w → lookupℕ w x ≡ false
lookup-beyond w       []      _       = Eq.refl
lookup-beyond zero    (b ∷ x) ()
lookup-beyond (suc w) (b ∷ x) (s≤s q) = lookup-beyond w x q

-- The string of zeros.
zeros : ∀ k → Bits k
zeros zero    = []
zeros (suc k) = false ∷ zeros k

xorB-self : ∀ (x : Bits k) → xorB x x ≡ zeros k
xorB-self []      = Eq.refl
xorB-self (b ∷ x) = Eq.cong₂ _∷_ (self b) (xorB-self x)
  where
  self : ∀ b → b xor b ≡ false
  self true  = Eq.refl
  self false = Eq.refl

------------------------------------------------------------------------
-- Flips

lookup-flip : ∀ p w (x : Bits n) → p < n → lookupℕ w (flipℕ p x) ≡ lookupℕ w x xor (w ≡ᵇ p)
lookup-flip zero    zero    (b ∷ x) _       = t-xor b
lookup-flip zero    (suc w) (b ∷ x) _       = Eq.sym (xor-f (lookupℕ w x))
lookup-flip (suc p) zero    (b ∷ x) _       = Eq.sym (xor-f b)
lookup-flip (suc p) (suc w) (b ∷ x) (s≤s q) = lookup-flip p w x q

flip-invol : ∀ p (x : Bits n) → flipℕ p (flipℕ p x) ≡ x
flip-invol p       []      = Eq.refl
flip-invol zero    (b ∷ x) = Eq.cong (_∷ x) (tt-xor b)
flip-invol (suc p) (b ∷ x) = Eq.cong (b ∷_) (flip-invol p x)

-- Flipping the bit just inserted.
flip-ins : ∀ p g (c : Bits k) → p ≤ k → flipℕ p (insertℕ p g c) ≡ insertℕ p (not g) c
flip-ins zero    g c        _       = Eq.refl
flip-ins (suc p) g (c₀ ∷ c) (s≤s q) = Eq.cong (c₀ ∷_) (flip-ins p g c q)

-- Removing the flipped bit, and removing above it.
remove-flip-same : ∀ p (x : Bits (suc n)) → p ≤ n → removeℕ p (flipℕ p x) ≡ removeℕ p x
remove-flip-same zero          (b ∷ x)     _       = Eq.refl
remove-flip-same (suc zero)    (b ∷ c ∷ x) _       = Eq.refl
remove-flip-same (suc (suc p)) (b ∷ c ∷ x) (s≤s q) =
  Eq.cong (b ∷_) (remove-flip-same (suc p) (c ∷ x) q)

remove-flip-below : ∀ i j (x : Bits (suc n)) → i < j → j ≤ n →
                    removeℕ j (flipℕ i x) ≡ flipℕ i (removeℕ j x)
remove-flip-below zero          (suc j) (b ∷ c ∷ x) _       _       = Eq.refl
remove-flip-below (suc zero)    (suc zero)    _               (s≤s ()) _
remove-flip-below (suc zero)    (suc (suc j)) (b ∷ c ∷ [])    _ (s≤s ())
remove-flip-below (suc zero)    (suc (suc j)) (b ∷ c ∷ d ∷ x) _ _ = Eq.refl
remove-flip-below (suc (suc i)) (suc (suc j)) (b ∷ c ∷ d ∷ x) (s≤s p) (s≤s q) =
  Eq.cong (b ∷_) (remove-flip-below (suc i) (suc j) (c ∷ d ∷ x) p q)

------------------------------------------------------------------------
-- Where two strings differ

infix 6 _∈ℕ_
_∈ℕ_ : ℕ → List ℕ → Bool
w ∈ℕ []       = false
w ∈ℕ (q ∷ qs) = (w ≡ᵇ q) ∨ (w ∈ℕ qs)

-- The wires numbered from i are all at least i.
diff-below : ∀ i w (x y : Bits n) → w < i → w ∈ℕ diffFrom i x y ≡ false
diff-below i w []          []          _ = Eq.refl
diff-below i w (true ∷ x)  (true ∷ y)  p = diff-below (suc i) w x y (m<n⇒m<1+n p)
diff-below i w (false ∷ x) (false ∷ y) p = diff-below (suc i) w x y (m<n⇒m<1+n p)
diff-below i w (true ∷ x)  (false ∷ y) p =
  Eq.cong₂ _∨_ (≡ᵇ-< w i p) (diff-below (suc i) w x y (m<n⇒m<1+n p))
diff-below i w (false ∷ x) (true ∷ y)  p =
  Eq.cong₂ _∨_ (≡ᵇ-< w i p) (diff-below (suc i) w x y (m<n⇒m<1+n p))

-- Each bit of y is that of x, flipped where they differ.
lookup-diffFrom : ∀ i w (x y : Bits n) →
                  lookupℕ w y ≡ lookupℕ w x xor ((i + w) ∈ℕ diffFrom i x y)
lookup-diffFrom i w       []      []      = Eq.refl
lookup-diffFrom i zero    (a ∷ x) (b ∷ y) rewrite +-identityʳ i = at0 a b
  where
  rest : i ∈ℕ diffFrom (suc i) x y ≡ false
  rest = diff-below (suc i) i x y (n<1+n i)

  at0 : ∀ a b → b ≡ a xor (i ∈ℕ diffFrom i (a ∷ x) (b ∷ y))
  at0 true  true  = Eq.cong (true xor_) (Eq.sym rest)
  at0 false false = Eq.sym rest
  at0 true  false = Eq.cong (λ v → true xor (v ∨ (i ∈ℕ diffFrom (suc i) x y)))
                            (Eq.sym (≡ᵇ-refl i))
  at0 false true  = Eq.cong (λ v → v ∨ (i ∈ℕ diffFrom (suc i) x y)) (Eq.sym (≡ᵇ-refl i))
lookup-diffFrom i (suc w) (a ∷ x) (b ∷ y) rewrite +-suc i w = atS a b
  where
  ih : lookupℕ w y ≡ lookupℕ w x xor (suc (i + w) ∈ℕ diffFrom (suc i) x y)
  ih = lookup-diffFrom (suc i) w x y

  atS : ∀ a b → lookupℕ w y ≡ lookupℕ w x xor (suc (i + w) ∈ℕ diffFrom i (a ∷ x) (b ∷ y))
  atS true  true  = ih
  atS false false = ih
  atS true  false = Eq.trans ih (Eq.cong (λ v → lookupℕ w x xor (v ∨ (suc (i + w) ∈ℕ diffFrom (suc i) x y)))
                                          (Eq.sym (≡ᵇ-suc+ i w)))
  atS false true  = Eq.trans ih (Eq.cong (λ v → lookupℕ w x xor (v ∨ (suc (i + w) ∈ℕ diffFrom (suc i) x y)))
                                          (Eq.sym (≡ᵇ-suc+ i w)))

lookup-diff : ∀ w (x y : Bits n) → lookupℕ w y ≡ lookupℕ w x xor (w ∈ℕ diff x y)
lookup-diff w x y = lookup-diffFrom 0 w x y

-- A string differing from x at exactly one wire is x flipped there.
diff-one : ∀ (x y : Bits n) p → diff x y ≡ p ∷ [] → (p < n) × (y ≡ flipℕ p x)
diff-one {n} x y p e = p<n , vec-ext y (flipℕ p x) bits
  where
  mem : ∀ w → w ∈ℕ diff x y ≡ (w ≡ᵇ p)
  mem w = Eq.trans (Eq.cong (w ∈ℕ_) e) (∨-f (w ≡ᵇ p))

  p<n : p < n
  p<n with p <? n
  ... | yes q = q
  ... | no ¬q = ⊥-elim (f≢t (begin
    false                                  ≡⟨ Eq.sym (lookup-beyond p y (≮⇒≥ ¬q)) ⟩
    lookupℕ p y                            ≡⟨ lookup-diff p x y ⟩
    lookupℕ p x xor (p ∈ℕ diff x y)        ≡⟨ Eq.cong₂ _xor_ (lookup-beyond p x (≮⇒≥ ¬q))
                                                (Eq.trans (mem p) (≡ᵇ-refl p)) ⟩
    true                                   ∎))
    where
    f≢t : false ≢ true
    f≢t ()

  bits : ∀ w → lookupℕ w y ≡ lookupℕ w (flipℕ p x)
  bits w = Eq.trans (lookup-diff w x y)
             (Eq.trans (Eq.cong (lookupℕ w x xor_) (mem w)) (Eq.sym (lookup-flip p w x p<n)))

------------------------------------------------------------------------
-- The H-pattern, read back

record HPat (a b c d : Bits n) (pb pc : ℕ) : Set where
  field
    db : diff a b ≡ pb ∷ []
    dc : diff a c ≡ pc ∷ []
    q₁ q₂ : ℕ
    dd : diff a d ≡ q₁ ∷ q₂ ∷ []
    qs : (((pb ≡ᵇ q₁) ∧ (pc ≡ᵇ q₂)) ∨ ((pb ≡ᵇ q₂) ∧ (pc ≡ᵇ q₁))) ≡ true
    za : lookupℕ pb a ≡ false
    zc : lookupℕ pc a ≡ false

private
  nj : ∀ {A : Set} {x : A} → nothing ≢ just x
  nj ()

  if-just : ∀ {A : Set} (t : Bool) (x y : A) →
            (if t then just x else nothing) ≡ just y → (t ≡ true) × (x ≡ y)
  if-just true  x .x Eq.refl = Eq.refl , Eq.refl
  if-just false x y  ()

  pair-l : ∀ {x y x′ y′ : ℕ} → (x , y) ≡ (x′ , y′) → x ≡ x′
  pair-l Eq.refl = Eq.refl

  pair-r : ∀ {x y x′ y′ : ℕ} → (x , y) ≡ (x′ , y′) → y ≡ y′
  pair-r Eq.refl = Eq.refl

hpat-inv : ∀ (a b c d : Bits n) pb pc → hpat a b c d ≡ just (pb , pc) → HPat a b c d pb pc
hpat-inv a b c d pb pc h with diff a b in e₁ | diff a c in e₂ | diff a d in e₃
... | []            | _             | _                 = ⊥-elim (nj h)
... | _ ∷ _ ∷ _     | _             | _                 = ⊥-elim (nj h)
... | _ ∷ []        | []            | _                 = ⊥-elim (nj h)
... | _ ∷ []        | _ ∷ _ ∷ _     | _                 = ⊥-elim (nj h)
... | _ ∷ []        | _ ∷ []        | []                = ⊥-elim (nj h)
... | _ ∷ []        | _ ∷ []        | _ ∷ []            = ⊥-elim (nj h)
... | _ ∷ []        | _ ∷ []        | _ ∷ _ ∷ _ ∷ _     = ⊥-elim (nj h)
... | pb′ ∷ []      | pc′ ∷ []      | q₁ ∷ q₂ ∷ []      = go (if-just _ _ _ h)
  where
  X : Bool
  X = ((pb′ ≡ᵇ q₁) ∧ (pc′ ≡ᵇ q₂)) ∨ ((pb′ ≡ᵇ q₂) ∧ (pc′ ≡ᵇ q₁))

  go : (X ∧ not (lookupℕ pb′ a) ∧ not (lookupℕ pc′ a)) ≡ true × ((pb′ , pc′) ≡ (pb , pc)) →
       HPat a b c d pb pc
  go (ct , ep) with pair-l ep | pair-r ep
  ... | Eq.refl | Eq.refl = record
    { db = e₁ ; dc = e₂ ; q₁ = q₁ ; q₂ = q₂ ; dd = e₃
    ; qs = ∧-l X _ ct
    ; za = not-t _ (∧-l _ _ (∧-r X _ ct))
    ; zc = not-t _ (∧-r _ _ (∧-r X _ ct))
    }

-- So the codes are a flipped at pb, at pc, and at both.
module Flips {a b c d : Bits n} {pb pc : ℕ} (H : HPat a b c d pb pc) where
  open HPat H

  pb<n : pb < n
  pb<n = proj₁ (diff-one a b pb db)

  pc<n : pc < n
  pc<n = proj₁ (diff-one a c pc dc)

  b-flip : b ≡ flipℕ pb a
  b-flip = proj₂ (diff-one a b pb db)

  c-flip : c ≡ flipℕ pc a
  c-flip = proj₂ (diff-one a c pc dc)

  -- The two wires differ as soon as b and c do.
  pb≢pc : b ≢ c → pb ≢ pc
  pb≢pc bc e = bc (Eq.trans b-flip (Eq.trans (Eq.cong (λ p → flipℕ p a) e) (Eq.sym c-flip)))

  private
    ∨-split : ∀ x y → x ∨ y ≡ true → (x ≡ true) ⊎ (y ≡ true)
    ∨-split true  y _ = inj₁ Eq.refl
    ∨-split false y e = inj₂ e

    ∨-comm′ : ∀ x y → x ∨ y ≡ y ∨ x
    ∨-comm′ true  true  = Eq.refl
    ∨-comm′ true  false = Eq.refl
    ∨-comm′ false true  = Eq.refl
    ∨-comm′ false false = Eq.refl

    -- The two wires of d are pb and pc.
    mem : ∀ w → w ∈ℕ diff a d ≡ (w ≡ᵇ pb) ∨ (w ≡ᵇ pc)
    mem w = Eq.trans (Eq.cong (w ∈ℕ_) dd)
              (Eq.trans (Eq.cong ((w ≡ᵇ q₁) ∨_) (∨-f (w ≡ᵇ q₂))) (which (∨-split _ _ qs)))
      where
      which : ((((pb ≡ᵇ q₁) ∧ (pc ≡ᵇ q₂)) ≡ true) ⊎ (((pb ≡ᵇ q₂) ∧ (pc ≡ᵇ q₁)) ≡ true)) →
              (w ≡ᵇ q₁) ∨ (w ≡ᵇ q₂) ≡ (w ≡ᵇ pb) ∨ (w ≡ᵇ pc)
      which (inj₁ e) =
        Eq.cong₂ (λ s t → (w ≡ᵇ s) ∨ (w ≡ᵇ t))
                 (Eq.sym (≡ᵇ-true pb q₁ (∧-l (pb ≡ᵇ q₁) (pc ≡ᵇ q₂) e)))
                 (Eq.sym (≡ᵇ-true pc q₂ (∧-r (pb ≡ᵇ q₁) (pc ≡ᵇ q₂) e)))
      which (inj₂ e) =
        Eq.trans (Eq.cong₂ (λ s t → (w ≡ᵇ s) ∨ (w ≡ᵇ t))
                           (Eq.sym (≡ᵇ-true pc q₁ (∧-r (pb ≡ᵇ q₂) (pc ≡ᵇ q₁) e)))
                           (Eq.sym (≡ᵇ-true pb q₂ (∧-l (pb ≡ᵇ q₂) (pc ≡ᵇ q₁) e))))
                 (∨-comm′ (w ≡ᵇ pc) (w ≡ᵇ pb))

    -- Flipping two different wires is xor with their union.
    two : ∀ x s t → (s ∧ t) ≡ false → (x xor t) xor s ≡ x xor (s ∨ t)
    two true  true  true  ()
    two false true  true  ()
    two true  true  false _ = Eq.refl
    two true  false true  _ = Eq.refl
    two true  false false _ = Eq.refl
    two false true  false _ = Eq.refl
    two false false true  _ = Eq.refl
    two false false false _ = Eq.refl

    both : pb ≢ pc → ∀ w → ((w ≡ᵇ pb) ∧ (w ≡ᵇ pc)) ≡ false
    both ne w with w ≡ᵇ pb in e₁ | w ≡ᵇ pc in e₂
    ... | true  | true  = ⊥-elim (ne (Eq.trans (Eq.sym (≡ᵇ-true w pb e₁)) (≡ᵇ-true w pc e₂)))
    ... | true  | false = Eq.refl
    ... | false | _     = Eq.refl

  d-flip : pb ≢ pc → d ≡ flipℕ pb (flipℕ pc a)
  d-flip ne = vec-ext d (flipℕ pb (flipℕ pc a)) bits
    where
    bits : ∀ w → lookupℕ w d ≡ lookupℕ w (flipℕ pb (flipℕ pc a))
    bits w = begin
      lookupℕ w d                                        ≡⟨ lookup-diff w a d ⟩
      lookupℕ w a xor (w ∈ℕ diff a d)                    ≡⟨ Eq.cong (lookupℕ w a xor_) (mem w) ⟩
      lookupℕ w a xor ((w ≡ᵇ pb) ∨ (w ≡ᵇ pc))            ≡⟨ Eq.sym (two (lookupℕ w a) _ _ (both ne w)) ⟩
      (lookupℕ w a xor (w ≡ᵇ pc)) xor (w ≡ᵇ pb)          ≡⟨ Eq.cong (_xor (w ≡ᵇ pb))
                                                              (Eq.sym (lookup-flip pc w a pc<n)) ⟩
      lookupℕ w (flipℕ pc a) xor (w ≡ᵇ pb)               ≡⟨ Eq.sym (lookup-flip pb w (flipℕ pc a) pb<n) ⟩
      lookupℕ w (flipℕ pb (flipℕ pc a))                  ∎

------------------------------------------------------------------------
-- Exchanging adjacent wires

swapBits : ℕ → Bits n → Bits n
swapBits zero    []          = []
swapBits zero    (a ∷ [])    = a ∷ []
swapBits zero    (a ∷ b ∷ x) = b ∷ a ∷ x
swapBits (suc p) []          = []
swapBits (suc p) (a ∷ x)     = a ∷ swapBits p x

swap-invol : ∀ p (x : Bits n) → swapBits p (swapBits p x) ≡ x
swap-invol zero    []          = Eq.refl
swap-invol zero    (a ∷ [])    = Eq.refl
swap-invol zero    (a ∷ b ∷ x) = Eq.refl
swap-invol (suc p) []          = Eq.refl
swap-invol (suc p) (a ∷ x)     = Eq.cong (a ∷_) (swap-invol p x)

-- The exchange of wires p and p + 1, on a string built with them.
swap-ins : ∀ p u t (c : Bits k) → p ≤ k →
           swapBits p (insertℕ (suc p) u (insertℕ p t c)) ≡ insertℕ (suc p) t (insertℕ p u c)
swap-ins zero    u t c        _       = Eq.refl
swap-ins (suc p) u t (c₀ ∷ c) (s≤s q) = Eq.cong (c₀ ∷_) (swap-ins p u t c q)

-- It moves a bit inserted at p + 1 down to p.
swap-down : ∀ p v (z : Bits (suc k)) → p ≤ k → swapBits p (insertℕ (suc p) v z) ≡ insertℕ p v z
swap-down zero    v (z₀ ∷ z) _       = Eq.refl
swap-down (suc p) v (z₀ ∷ z) (s≤s q) = Eq.cong (z₀ ∷_) (swap-down p v z q)

------------------------------------------------------------------------
-- Composites along a list, the left one acting first

run : {A : Set} → (A → Bits n → Bits n) → List A → Bits n → Bits n
run f []       x = x
run f (a ∷ as) x = run f as (f a x)

run-∷ʳ : ∀ {A : Set} (f : A → Bits n → Bits n) (as : List A) (a : A) (x : Bits n) →
         run f (as ∷ʳ a) x ≡ f a (run f as x)
run-∷ʳ f []       a x = Eq.refl
run-∷ʳ f (b ∷ as) a x = run-∷ʳ f as a (f b x)

-- A composite is undone by the reverse composite of the inverses.
tele : ∀ {A : Set} (f g : A → Bits n → Bits n) (as : List A) →
       (∀ a y → g a (f a y) ≡ y) → ∀ x → run g (reverse as) (run f as x) ≡ x
tele f g []       inv x = Eq.refl
tele f g (a ∷ as) inv x = begin
  run g (reverse (a ∷ as)) (run f as (f a x))
    ≡⟨ Eq.cong (λ l → run g l (run f as (f a x))) (unfold-reverse a as) ⟩
  run g (reverse as ∷ʳ a) (run f as (f a x))
    ≡⟨ run-∷ʳ g (reverse as) a (run f as (f a x)) ⟩
  g a (run g (reverse as) (run f as (f a x)))
    ≡⟨ Eq.cong (g a) (tele f g as inv (f a x)) ⟩
  g a (f a x)
    ≡⟨ inv a x ⟩
  x ∎

------------------------------------------------------------------------
-- Ranges

private
  applyUpTo-∷ʳ : ∀ (f : ℕ → ℕ) k → applyUpTo f (suc k) ≡ applyUpTo f k ∷ʳ f k
  applyUpTo-∷ʳ f zero    = Eq.refl
  applyUpTo-∷ʳ f (suc k) = Eq.cong (f 0 ∷_) (applyUpTo-∷ʳ (λ x → f (suc x)) k)

  applyUpTo-suc : ∀ (f : ℕ → ℕ) k → applyUpTo (λ x → suc (f x)) k ≡ map suc (applyUpTo f k)
  applyUpTo-suc f zero    = Eq.refl
  applyUpTo-suc f (suc k) = Eq.cong (suc (f 0) ∷_) (applyUpTo-suc (λ x → f (suc x)) k)

  map-∷ʳ : ∀ (f : ℕ → ℕ) xs x → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
  map-∷ʳ f []       x = Eq.refl
  map-∷ʳ f (y ∷ xs) x = Eq.cong (f y ∷_) (map-∷ʳ f xs x)

  rev-∷ʳ : ∀ (xs : List ℕ) x → reverse (xs ∷ʳ x) ≡ x ∷ reverse xs
  rev-∷ʳ xs x = reverse-++ xs (x ∷ [])

  lt-∸ : ∀ a b t → t < b ∸ a → a + t < b
  lt-∸ zero    b       t p       = p
  lt-∸ (suc a) zero    t ()
  lt-∸ (suc a) (suc b) t p       = s≤s (lt-∸ a b t p)

range↑-suc : ∀ a b → a ≤ b → range↑ a (suc b) ≡ range↑ a b ∷ʳ b
range↑-suc a b a≤b = begin
  map (a +_) (upTo (suc b ∸ a))                ≡⟨ Eq.cong (λ k → map (a +_) (upTo k)) (+-∸-assoc 1 a≤b) ⟩
  map (a +_) (upTo (suc (b ∸ a)))              ≡⟨ Eq.cong (map (a +_)) (applyUpTo-∷ʳ (λ x → x) (b ∸ a)) ⟩
  map (a +_) (upTo (b ∸ a) ∷ʳ (b ∸ a))         ≡⟨ map-∷ʳ (a +_) (upTo (b ∸ a)) (b ∸ a) ⟩
  map (a +_) (upTo (b ∸ a)) ∷ʳ (a + (b ∸ a))   ≡⟨ Eq.cong (map (a +_) (upTo (b ∸ a)) ∷ʳ_) (m+[n∸m]≡n a≤b) ⟩
  range↑ a b ∷ʳ b                              ∎

range↓-suc : ∀ a b → a ≤ b → range↓ a (suc b) ≡ b ∷ range↓ a b
range↓-suc a b a≤b = Eq.trans (Eq.cong reverse (range↑-suc a b a≤b)) (rev-∷ʳ (range↑ a b) b)

range↓-refl : ∀ a → range↓ a a ≡ []
range↓-refl a = Eq.cong (λ k → reverse (map (a +_) (upTo k))) (n∸n≡0 a)

all-range↑ : ∀ {P : ℕ → Set} a b → (∀ t → a ≤ t → t < b → P t) → All P (range↑ a b)
all-range↑ a b h = map⁺ (applyUpTo⁺₁ (λ x → x) (b ∸ a) (λ {t} lt → h (a + t) (m≤m+n a t) (lt-∸ a b t lt)))

all-rev : ∀ {P : ℕ → Set} {xs : List ℕ} → All P xs → All P (reverse xs)
all-rev {xs = []}     []       = []
all-rev {xs = x ∷ xs} (p ∷ ps) = Eq.subst (All _) (Eq.sym (unfold-reverse x xs)) (∷ʳ⁺ (all-rev ps) p)

all-range↓ : ∀ {P : ℕ → Set} a b → (∀ t → a ≤ t → t < b → P t) → All P (range↓ a b)
all-range↓ a b h = all-rev (all-range↑ a b h)

------------------------------------------------------------------------
-- The swap network

-- A pair of exchanges, k then k + 1, and its inverse.
pairDn pairUp : ℕ → Bits n → Bits n
pairDn q x = swapBits (suc q) (swapBits q x)
pairUp q x = swapBits q (swapBits (suc q) x)

-- Carrying a bit inserted at j down to i + 1, one exchange at a time.
bubble : ∀ i j v (z : Bits k) → suc i ≤ j → j ≤ k →
         run swapBits (range↓ (suc i) j) (insertℕ j v z) ≡ insertℕ (suc i) v z
bubble i zero    v z () _
bubble i (suc j) v z (s≤s i≤j) j≤k with m≤n⇒m<n∨m≡n i≤j
... | inj₂ Eq.refl = Eq.cong (λ l → run swapBits l (insertℕ (suc i) v z)) (range↓-refl (suc i))
... | inj₁ i<j with z | j≤k
...   | z₀ ∷ z′ | s≤s j≤k′ = begin
  run swapBits (range↓ (suc i) (suc j)) (insertℕ (suc j) v (z₀ ∷ z′))
    ≡⟨ Eq.cong (λ l → run swapBits l (insertℕ (suc j) v (z₀ ∷ z′))) (range↓-suc (suc i) j i<j) ⟩
  run swapBits (range↓ (suc i) j) (swapBits j (insertℕ (suc j) v (z₀ ∷ z′)))
    ≡⟨ Eq.cong (run swapBits (range↓ (suc i) j)) (swap-down j v (z₀ ∷ z′) j≤k′) ⟩
  run swapBits (range↓ (suc i) j) (insertℕ j v (z₀ ∷ z′))
    ≡⟨ bubble i j v (z₀ ∷ z′) i<j (s≤s′ j≤k′) ⟩
  insertℕ (suc i) v (z₀ ∷ z′) ∎
  where
  s≤s′ : ∀ {a b} → a ≤ b → a ≤ suc b
  s≤s′ z≤n     = z≤n
  s≤s′ (s≤s p) = s≤s (s≤s′ p)

-- One pair of exchanges moves the two bits at q + 1, q + 2 down to q, q + 1.
private
  pair-step : ∀ q u v (r : Bits (suc k)) → q ≤ k →
              pairDn q (insertℕ (suc q) u (insertℕ (suc q) v r)) ≡ insertℕ q u (insertℕ q v r)
  pair-step {k} q u v r q≤k = begin
    swapBits (suc q) (swapBits q (insertℕ (suc q) u (insertℕ (suc q) v r)))
      ≡⟨ Eq.cong (swapBits (suc q)) (swap-down q u (insertℕ (suc q) v r) (le q≤k)) ⟩
    swapBits (suc q) (insertℕ q u (insertℕ (suc q) v r))
      ≡⟨ Eq.cong (swapBits (suc q)) (insert-swap (suc q) q v u r (le ≤-refl) (s≤s q≤k)) ⟩
    swapBits (suc q) (insertℕ (suc (suc q)) v (insertℕ q u r))
      ≡⟨ swap-down (suc q) v (insertℕ q u r) (s≤s q≤k) ⟩
    insertℕ (suc q) v (insertℕ q u r)
      ≡⟨ Eq.sym (insert-swap q q v u r ≤-refl (le q≤k)) ⟩
    insertℕ q u (insertℕ q v r) ∎
    where
    le : ∀ {a b} → a ≤ b → a ≤ suc b
    le z≤n     = z≤n
    le (s≤s p) = s≤s (le p)

-- Carrying the pair at i, i + 1 down to 0, 1.
pairdown : ∀ i u v (r : Bits k) → i ≤ k →
           run pairDn (range↓ 0 i) (insertℕ i u (insertℕ i v r)) ≡ u ∷ v ∷ r
pairdown zero    u v r _ = Eq.cong (λ l → run pairDn l (u ∷ v ∷ r)) (range↓-refl 0)
pairdown (suc i) u v (r₀ ∷ r) (s≤s i≤k) = begin
  run pairDn (range↓ 0 (suc i)) (insertℕ (suc i) u (insertℕ (suc i) v (r₀ ∷ r)))
    ≡⟨ Eq.cong (λ l → run pairDn l (insertℕ (suc i) u (insertℕ (suc i) v (r₀ ∷ r))))
               (range↓-suc 0 i z≤n) ⟩
  run pairDn (range↓ 0 i) (pairDn i (insertℕ (suc i) u (insertℕ (suc i) v (r₀ ∷ r))))
    ≡⟨ Eq.cong (run pairDn (range↓ 0 i)) (pair-step i u v (r₀ ∷ r) i≤k) ⟩
  run pairDn (range↓ 0 i) (insertℕ i u (insertℕ i v (r₀ ∷ r)))
    ≡⟨ pairdown i u v (r₀ ∷ r) (le i≤k) ⟩
  u ∷ v ∷ r₀ ∷ r ∎
  where
  le : ∀ {a b} → a ≤ b → a ≤ suc b
  le z≤n     = z≤n
  le (s≤s p) = s≤s (le p)

-- The network carries wires i < j to wires 0 and 1, the others keeping
-- their order.
network : ∀ i j (x : Bits (suc (suc k))) → i < j → j ≤ suc k →
          run pairDn (range↓ 0 i) (run swapBits (range↓ (suc i) j) x)
          ≡ lookupℕ i x ∷ lookupℕ j x ∷ removeℕ i (removeℕ j x)
network {k} i j x i<j j≤k = begin
  run pairDn (range↓ 0 i) (run swapBits (range↓ (suc i) j) x)
    ≡⟨ Eq.cong (λ y → run pairDn (range↓ 0 i) (run swapBits (range↓ (suc i) j) y))
               (Eq.sym (insert-lookup-remove j x j≤k)) ⟩
  run pairDn (range↓ 0 i) (run swapBits (range↓ (suc i) j) (insertℕ j xj R))
    ≡⟨ Eq.cong (run pairDn (range↓ 0 i)) (bubble i j xj R i<j j≤k) ⟩
  run pairDn (range↓ 0 i) (insertℕ (suc i) xj R)
    ≡⟨ Eq.cong (λ y → run pairDn (range↓ 0 i) (insertℕ (suc i) xj y)) (Eq.sym R-split) ⟩
  run pairDn (range↓ 0 i) (insertℕ (suc i) xj (insertℕ i xi r))
    ≡⟨ Eq.cong (run pairDn (range↓ 0 i)) (Eq.sym (insert-swap i i xj xi r ≤-refl i≤k)) ⟩
  run pairDn (range↓ 0 i) (insertℕ i xi (insertℕ i xj r))
    ≡⟨ pairdown i xi xj r i≤k ⟩
  xi ∷ xj ∷ r ∎
  where
  xi xj : Bool
  xi = lookupℕ i x
  xj = lookupℕ j x

  R : Bits (suc k)
  R = removeℕ j x

  r : Bits k
  r = removeℕ i R

  i≤k : i ≤ k
  i≤k = ≤-pred′ (≤-trans′ i<j j≤k)
    where
    ≤-trans′ : ∀ {a b c} → a < b → b ≤ c → a < c
    ≤-trans′ (s≤s z≤n)     (s≤s _)   = s≤s z≤n
    ≤-trans′ (s≤s (s≤s p)) (s≤s q)   = s≤s (≤-trans′ (s≤s p) q)
    ≤-pred′ : ∀ {a b} → suc a ≤ suc b → a ≤ b
    ≤-pred′ (s≤s p) = p

  R-split : insertℕ i xi r ≡ R
  R-split = Eq.trans (Eq.cong (λ b → insertℕ i b r) (Eq.sym (lookup-remove-below j i x i<j j≤k)))
                     (insert-lookup-remove i R i≤k)

------------------------------------------------------------------------
-- Conditional flips, and the negations

cflip : Bool → ℕ → Bits n → Bits n
cflip true  w x = flipℕ w x
cflip false w x = x

cflip-invol : ∀ b w (x : Bits n) → cflip b w (cflip b w x) ≡ x
cflip-invol true  w x = flip-invol w x
cflip-invol false w x = Eq.refl

private
  cflip-2 : ∀ b t u v (y : Bits n) → cflip b (suc (suc t)) (u ∷ v ∷ y) ≡ u ∷ v ∷ cflip b t y
  cflip-2 true  t u v y = Eq.refl
  cflip-2 false t u v y = Eq.refl

  cflip-1 : ∀ b t h (y : Bits n) → cflip b (suc t) (h ∷ y) ≡ h ∷ cflip b t y
  cflip-1 true  t h y = Eq.refl
  cflip-1 false t h y = Eq.refl

  cflip-0 : ∀ c r (y : Bits n) → cflip c 0 (r ∷ y) ≡ (c xor r) ∷ y
  cflip-0 true  r y = Eq.refl
  cflip-0 false r y = Eq.refl

  -- Flips at the wires of a list, shifted up past a prefix.
  shift2 : ∀ (cs : Bits k) (L : List ℕ) u v (y : Bits n) →
           run (λ w → cflip (lookupℕ (w ∸ 2) cs) w) (map (2 +_) L) (u ∷ v ∷ y)
           ≡ u ∷ v ∷ run (λ t → cflip (lookupℕ t cs) t) L y
  shift2 cs []      u v y = Eq.refl
  shift2 cs (t ∷ L) u v y =
    Eq.trans (Eq.cong (run _ (map (2 +_) L)) (cflip-2 (lookupℕ t cs) t u v y))
             (shift2 cs L u v (cflip (lookupℕ t cs) t y))

  shift1 : ∀ c₀ (cs : Bits k) (L : List ℕ) h (y : Bits n) →
           run (λ t → cflip (lookupℕ t (c₀ ∷ cs)) t) (map suc L) (h ∷ y)
           ≡ h ∷ run (λ t → cflip (lookupℕ t cs) t) L y
  shift1 c₀ cs []      h y = Eq.refl
  shift1 c₀ cs (t ∷ L) h y =
    Eq.trans (Eq.cong (run _ (map suc L)) (cflip-1 (lookupℕ t cs) t h y))
             (shift1 c₀ cs L h (cflip (lookupℕ t cs) t y))

  flips : ∀ (cs r : Bits k) → run (λ t → cflip (lookupℕ t cs) t) (upTo k) r ≡ xorB cs r
  flips []        []       = Eq.refl
  flips {suc k} (c₀ ∷ cs) (r₀ ∷ r) = begin
    run F (applyUpTo (λ x → suc x) k) (cflip c₀ 0 (r₀ ∷ r))
      ≡⟨ Eq.cong (run F (applyUpTo (λ x → suc x) k)) (cflip-0 c₀ r₀ r) ⟩
    run F (applyUpTo (λ x → suc x) k) ((c₀ xor r₀) ∷ r)
      ≡⟨ Eq.cong (λ l → run F l ((c₀ xor r₀) ∷ r)) (applyUpTo-suc (λ x → x) k) ⟩
    run F (map suc (upTo k)) ((c₀ xor r₀) ∷ r)
      ≡⟨ shift1 c₀ cs (upTo k) (c₀ xor r₀) r ⟩
    (c₀ xor r₀) ∷ run (λ t → cflip (lookupℕ t cs) t) (upTo k) r
      ≡⟨ Eq.cong ((c₀ xor r₀) ∷_) (flips cs r) ⟩
    (c₀ xor r₀) ∷ xorB cs r ∎
    where
    F : ℕ → Bits (suc k) → Bits (suc k)
    F t = cflip (lookupℕ t (c₀ ∷ cs)) t

-- The negations of Equations (36) and (37): flipping wire w ≥ 2 when
-- the control there is 1 xors the controls into the string.
negs : ∀ (cs r : Bits k) u v →
       run (λ w → cflip (lookupℕ (w ∸ 2) cs) w) (range↑ 2 (suc (suc k))) (u ∷ v ∷ r)
       ≡ u ∷ v ∷ xorB cs r
negs {k} cs r u v =
  Eq.trans (shift2 cs (upTo k) u v r) (Eq.cong (λ y → u ∷ v ∷ y) (flips cs r))
