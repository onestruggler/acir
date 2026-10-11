------------------------------------------------------------------------
-- Presentations of groups
--
-- Two Gray-code steps that are not neighbours differ off both targets
-- (Clément, Appendix E.5; used by the rule (32))
--
-- The decoded letter of (−1)_[a] X_[a,a+1] is a rotation on the wire
-- t_a where the codes of a and a + 1 differ, controlled by the other
-- bits of the code of a.  For a + 1 < b the letters of a and b commute
-- because their colourings differ on a wire off both targets: were the
-- codes of a and b equal off t_a and t_b, making a's code agree with
-- b's at t_a (by flipping it there, which gives the code of a + 1) and
-- then b's with the result at t_b (the code of b + 1) would make the
-- codes of one of a, a + 1 and of one of b, b + 1 equal — which the
-- injectivity of the code forbids, all four being below 2 ^ N and the
-- first two below the last two (`witness`).  The wire is found by a
-- search (`find`), whose failure is that agreement.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Lemma88.GrayWitness {m : ℕ} where

open import Data.Bool using (Bool ; true ; false ; not ; _∨_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Maybe using (Maybe ; just ; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (zero ; suc ; _<_ ; _≤_ ; _≡ᵇ_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (m≤n⇒m<n∨m≡n ; <⇒≤ ; ≤-trans ; <-trans ; n<1+n ; <-irrefl ; 0≢1+n ; suc-injective)
import Data.Nat.Properties
open import Data.Product using (Σ ; Σ-syntax ; _×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (toBits ; fromBits ; fromBits-toBits ; gray ; ungray ; ungray-gray ; parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep
  using (incr ; firstZero ; incr-first ; toBits-suc ; flipAt ; gray-compl)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Decoding using (gcode)

private
  N : ℕ
  N = ₃₊ m

------------------------------------------------------------------------
-- The step of the code

-- The wire where the codes of a and a + 1 differ.
tgt : ℕ → ℕ
tgt a = firstZero (toBits N a)

private
  fz≤ : ∀ {n} (s : Bits n) → firstZero s ≤ n
  fz≤ []          = z≤n
  fz≤ (false ∷ s) = z≤n
  fz≤ (true ∷ s)  = s≤s (fz≤ s)

  incr-full : ∀ {n} (s : Bits n) → firstZero s ≡ n → incr s ≡ replicate n false
  incr-full []          _ = Eq.refl
  incr-full (true ∷ s)  e = Eq.cong (false ∷_) (incr-full s (suc-injective e))

  toBits-0 : ∀ n → toBits n 0 ≡ replicate n false
  toBits-0 zero    = Eq.refl
  toBits-0 (suc n) = Eq.cong (false ∷_) (toBits-0 n)

tgt< : ∀ a → suc a < 2 ^ N → tgt a < N
tgt< a bnd with m≤n⇒m<n∨m≡n (fz≤ (toBits N a))
... | inj₁ lt = lt
... | inj₂ eq = ⊥-elim (0≢1+n (Eq.trans (Eq.sym (fromBits-toBits N 0 pos))
                                 (Eq.trans (Eq.cong fromBits e) (fromBits-toBits N (suc a) bnd))))
  where
  pos : 0 < 2 ^ N
  pos = ≤-trans (s≤s z≤n) (<⇒≤ bnd)
  e : toBits N 0 ≡ toBits N (suc a)
  e = Eq.trans (toBits-0 N) (Eq.sym (Eq.trans (toBits-suc N a) (incr-full (toBits N a) eq)))

gstep : ∀ a → suc a < 2 ^ N → gcode {m} (suc a) ≡ flipAt (tgt a) (gcode a)
gstep a bnd = Eq.trans (Eq.cong gray (Eq.trans (toBits-suc N a) (incr-first (toBits N a) (tgt< a bnd))))
                       (gray-compl (tgt a) (toBits N a) (tgt< a bnd))

gcode-inj : ∀ {a b} → a < 2 ^ N → b < 2 ^ N → gcode {m} a ≡ gcode b → a ≡ b
gcode-inj {a} {b} a< b< e =
  Eq.trans (Eq.sym (fromBits-toBits N a a<))
    (Eq.trans (Eq.cong fromBits (Eq.trans (Eq.sym (ungray-gray (toBits N a)))
                                  (Eq.trans (Eq.cong ungray e) (ungray-gray (toBits N b)))))
              (fromBits-toBits N b b<))

------------------------------------------------------------------------
-- Bits

lookup-flip-same : ∀ {n} i (s : Bits n) → i < n → lookupℕ i (flipAt i s) ≡ not (lookupℕ i s)
lookup-flip-same zero    (b ∷ s) _       = Eq.refl
lookup-flip-same (suc i) (b ∷ s) (s≤s p) = lookup-flip-same i s p

lookup-flip-other : ∀ {n} i j (s : Bits n) → j ≢ i → lookupℕ j (flipAt i s) ≡ lookupℕ j s
lookup-flip-other i       j       []      _  = Eq.refl
lookup-flip-other zero    zero    (b ∷ s) ne = ⊥-elim (ne Eq.refl)
lookup-flip-other zero    (suc j) (b ∷ s) _  = Eq.refl
lookup-flip-other (suc i) zero    (b ∷ s) _  = Eq.refl
lookup-flip-other (suc i) (suc j) (b ∷ s) ne = lookup-flip-other i j s (λ e → ne (Eq.cong suc e))

bits-ext : ∀ {n} (s s′ : Bits n) → (∀ j → j < n → lookupℕ j s ≡ lookupℕ j s′) → s ≡ s′
bits-ext []      []       _ = Eq.refl
bits-ext (a ∷ s) (b ∷ s′) h = Eq.cong₂ _∷_ (h 0 (s≤s z≤n)) (bits-ext s s′ (λ j j< → h (suc j) (s≤s j<)))

private
  -- Boolean equality of bits, and of numbers.
  same : Bool → Bool → Bool
  same true  b = b
  same false b = not b

  same-true : ∀ a b → same a b ≡ true → a ≡ b
  same-true true  true  _ = Eq.refl
  same-true false false _ = Eq.refl

  same-false : ∀ a b → same a b ≡ false → a ≢ b
  same-false true  true  () _
  same-false true  false _  ()
  same-false false true  _  ()
  same-false false false () _

  ≡ᵇ-refl : ∀ x → (x ≡ᵇ x) ≡ true
  ≡ᵇ-refl zero    = Eq.refl
  ≡ᵇ-refl (suc x) = ≡ᵇ-refl x

  ≡ᵇ-≢ : ∀ x y → x ≢ y → (x ≡ᵇ y) ≡ false
  ≡ᵇ-≢ zero    zero    ne = ⊥-elim (ne Eq.refl)
  ≡ᵇ-≢ zero    (suc y) _  = Eq.refl
  ≡ᵇ-≢ (suc x) zero    _  = Eq.refl
  ≡ᵇ-≢ (suc x) (suc y) ne = ≡ᵇ-≢ x y (λ e → ne (Eq.cong suc e))

  ∨-false₁ : ∀ a b → (a ∨ b) ≡ false → a ≡ false
  ∨-false₁ false b _ = Eq.refl

  ∨-false₂ : ∀ a b → (a ∨ b) ≡ false → b ≡ false
  ∨-false₂ false b e = e

  t≢f : true ≢ false
  t≢f ()

------------------------------------------------------------------------
-- The search for a wire where two strings differ, off excluded wires

private
  pick : Bool → Bool → Maybe ℕ → Maybe ℕ
  pick false false _ = just 0
  pick false true  r = Maybe.map suc r
  pick true  _     r = Maybe.map suc r

  find : ∀ {n} → (ℕ → Bool) → Bits n → Bits n → Maybe ℕ
  find ex []      []       = nothing
  find ex (a ∷ s) (b ∷ s′) = pick (ex 0) (same a b) (find (λ j → ex (suc j)) s s′)

  map-just : ∀ {r : Maybe ℕ} {j} → Maybe.map suc r ≡ just j → Σ ℕ λ j′ → (r ≡ just j′) × (j ≡ suc j′)
  map-just {just j′} Eq.refl = j′ , Eq.refl , Eq.refl
  map-just {nothing} ()

  map-nothing : ∀ {r : Maybe ℕ} → Maybe.map suc r ≡ nothing → r ≡ nothing
  map-nothing {nothing} _ = Eq.refl
  map-nothing {just _}  ()

  find-sound : ∀ {n} ex (s s′ : Bits n) j → find ex s s′ ≡ just j →
               (j < n) × (ex j ≡ false) × (lookupℕ j s ≢ lookupℕ j s′)
  find-sound ex []      []       j ()
  find-sound {suc n} ex (a ∷ s) (b ∷ s′) j e = go (ex 0) (same a b) Eq.refl Eq.refl e
    where
    rest : Maybe ℕ
    rest = find (λ j → ex (suc j)) s s′
    tail : ∀ j → Maybe.map suc rest ≡ just j → (j < suc n) × (ex j ≡ false) × (lookupℕ j (a ∷ s) ≢ lookupℕ j (b ∷ s′))
    tail j e′ with map-just {rest} e′
    ... | j′ , r , Eq.refl with find-sound (λ j → ex (suc j)) s s′ j′ r
    ...   | j′< , exj , ne = s≤s j′< , exj , ne
    go : ∀ x y → ex 0 ≡ x → same a b ≡ y → pick x y rest ≡ just j →
         (j < suc n) × (ex j ≡ false) × (lookupℕ j (a ∷ s) ≢ lookupℕ j (b ∷ s′))
    go false false ex0 ab Eq.refl = s≤s z≤n , ex0 , same-false a b ab
    go false true  _   _  e′      = tail j e′
    go true  y     _   _  e′      = tail j e′

  find-complete : ∀ {n} ex (s s′ : Bits n) → find ex s s′ ≡ nothing →
                  ∀ j → j < n → ex j ≡ false → lookupℕ j s ≡ lookupℕ j s′
  find-complete ex []      []       e j ()  exj
  find-complete {suc n} ex (a ∷ s) (b ∷ s′) e j j< exj = go (ex 0) (same a b) Eq.refl Eq.refl e j j< exj
    where
    rest : Maybe ℕ
    rest = find (λ j → ex (suc j)) s s′
    go : ∀ x y → ex 0 ≡ x → same a b ≡ y → pick x y rest ≡ nothing →
         ∀ j → j < suc n → ex j ≡ false → lookupℕ j (a ∷ s) ≡ lookupℕ j (b ∷ s′)
    go false false _   _  () _ _ _
    go x     true  _   ab e′ zero    _       _   = same-true a b ab
    go true  false ex0 _  e′ zero    _       exj = ⊥-elim (t≢f (Eq.trans (Eq.sym ex0) exj))
    go false true  _   _  e′ (suc j) (s≤s p) exj = find-complete (λ j → ex (suc j)) s s′ (map-nothing {rest} e′) j p exj
    go true  y     _   _  e′ (suc j) (s≤s p) exj = find-complete (λ j → ex (suc j)) s s′ (map-nothing {rest} e′) j p exj

------------------------------------------------------------------------
-- The witness

private
  -- s made to agree with s′ at i: flipped there or not, by the bit b of
  -- their agreement.
  adjB : Bool → ℕ → Bits N → Bits N
  adjB true  i s = s
  adjB false i s = flipAt i s

  adj : ℕ → Bits N → Bits N → Bits N
  adj i s s′ = adjB (same (lookupℕ i s) (lookupℕ i s′)) i s

  adj-cases : ∀ i s s′ → (adj i s s′ ≡ s) ⊎ (adj i s s′ ≡ flipAt i s)
  adj-cases i s s′ = go (same (lookupℕ i s) (lookupℕ i s′))
    where
    go : ∀ b → (adjB b i s ≡ s) ⊎ (adjB b i s ≡ flipAt i s)
    go true  = inj₁ Eq.refl
    go false = inj₂ Eq.refl

  not-≢ : ∀ {a b} → a ≢ b → not a ≡ b
  not-≢ {true}  {true}  ne = ⊥-elim (ne Eq.refl)
  not-≢ {true}  {false} _  = Eq.refl
  not-≢ {false} {true}  _  = Eq.refl
  not-≢ {false} {false} ne = ⊥-elim (ne Eq.refl)

  adj-same : ∀ i s s′ → i < N → lookupℕ i (adj i s s′) ≡ lookupℕ i s′
  adj-same i s s′ i< = go (same (lookupℕ i s) (lookupℕ i s′)) Eq.refl
    where
    go : ∀ b → same (lookupℕ i s) (lookupℕ i s′) ≡ b → lookupℕ i (adjB b i s) ≡ lookupℕ i s′
    go true  e = same-true _ _ e
    go false e = Eq.trans (lookup-flip-same i s i<) (not-≢ (same-false _ _ e))

  adj-other : ∀ i j s s′ → j ≢ i → lookupℕ j (adj i s s′) ≡ lookupℕ j s
  adj-other i j s s′ ne = go (same (lookupℕ i s) (lookupℕ i s′))
    where
    go : ∀ b → lookupℕ j (adjB b i s) ≡ lookupℕ j s
    go true  = Eq.refl
    go false = lookup-flip-other i j s ne

witness : ∀ a b → suc a < b → suc b < 2 ^ N →
          Σ ℕ λ j → (j < N) × (j ≢ tgt a) × (j ≢ tgt b) × (lookupℕ j (gcode {m} a) ≢ lookupℕ j (gcode b))
witness a b ab bb = decide (find ex G H) Eq.refl
  where
  p q : ℕ
  p = tgt a
  q = tgt b

  G H : Bits N
  G = gcode a
  H = gcode b

  ex : ℕ → Bool
  ex j = (j ≡ᵇ p) ∨ (j ≡ᵇ q)

  b< : b < 2 ^ N
  b< = <-trans (n<1+n b) bb

  a< : suc a < 2 ^ N
  a< = <-trans ab b<

  ex-false : ∀ j → j ≢ p → j ≢ q → ex j ≡ false
  ex-false j jp jq = Eq.cong₂ _∨_ (≡ᵇ-≢ j p jp) (≡ᵇ-≢ j q jq)

  ex-p : ∀ j → ex j ≡ false → j ≢ p
  ex-p j e Eq.refl = t≢f (Eq.trans (Eq.sym (≡ᵇ-refl j)) (∨-false₁ (j ≡ᵇ j) (j ≡ᵇ q) e))

  ex-q : ∀ j → ex j ≡ false → j ≢ q
  ex-q j e Eq.refl = t≢f (Eq.trans (Eq.sym (≡ᵇ-refl j)) (∨-false₂ (j ≡ᵇ p) (j ≡ᵇ j) e))

  -- The two adjusted codes.
  G′ H′ : Bits N
  G′ = adj p G H
  H′ = adj q H G′

  codeG : Σ ℕ λ i → (i ≤ suc a) × (G′ ≡ gcode i)
  codeG with adj-cases p G H
  ... | inj₁ e = a , <⇒≤ (n<1+n a) , e
  ... | inj₂ e = suc a , Data.Nat.Properties.≤-refl , Eq.trans e (Eq.sym (gstep a a<))

  codeH : Σ ℕ λ i → (b ≤ i) × (i < 2 ^ N) × (H′ ≡ gcode i)
  codeH with adj-cases q H G′
  ... | inj₁ e = b , Data.Nat.Properties.≤-refl , b< , e
  ... | inj₂ e = suc b , <⇒≤ (n<1+n b) , bb , Eq.trans e (Eq.sym (gstep b bb))

  contra : (∀ j → j < N → ex j ≡ false → lookupℕ j G ≡ lookupℕ j H) → ⊥
  contra agree with codeG | codeH
  ... | i , i≤ , eG | i′ , i′≥ , i′< , eH =
    <-irrefl Eq.refl (Eq.subst (_< i′) ii′ (Data.Nat.Properties.<-≤-trans (Data.Nat.Properties.≤-<-trans i≤ ab) i′≥))
    where
    pointwise : ∀ j → j < N → lookupℕ j G′ ≡ lookupℕ j H′
    pointwise j j< with j Data.Nat.Properties.≟ q
    ... | yes Eq.refl = Eq.sym (adj-same q H G′ j<)
    ... | no jq with j Data.Nat.Properties.≟ p
    ...   | yes Eq.refl = Eq.trans (adj-same p G H j<) (Eq.sym (adj-other q j H G′ jq))
    ...   | no jp = Eq.trans (adj-other p j G H jp)
                      (Eq.trans (agree j j< (ex-false j jp jq)) (Eq.sym (adj-other q j H G′ jq)))
    ii′ : i ≡ i′
    ii′ = gcode-inj (Data.Nat.Properties.≤-<-trans i≤ a<) i′<
            (Eq.trans (Eq.sym eG) (Eq.trans (bits-ext G′ H′ pointwise) eH))

  decide : ∀ r → find ex G H ≡ r →
           Σ ℕ λ j → (j < N) × (j ≢ p) × (j ≢ q) × (lookupℕ j G ≢ lookupℕ j H)
  decide (just j) e with find-sound ex G H j e
  ... | j< , exj , ne = j , j< , ex-p j exj , ex-q j exj , ne
  decide nothing  e = ⊥-elim (contra (find-complete ex G H e))

-- Two consecutive steps have different targets: one of a, a + 1 is even,
-- and the target of an even step is wire 0, of an odd one not.
tgt-apart : ∀ a → tgt a ≢ tgt (suc a)
tgt-apart a with parity a
... | false = λ ()
... | true  = λ ()
