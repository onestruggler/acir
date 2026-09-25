------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoding of n-qubit circuits into words over P (Clément,
-- Definition 8.2), and the words of Appendix A.4.1
--
-- A gate on wire p, with k = n − 1 − p wires above it, is encoded as a
-- product, over every assignment of the other wires, of the letter of
-- P that is the gate on the basis vectors of that assignment: the
-- letter pairs the two values of one further wire, the one just below
-- the gate, or the top wire when the gate is on wire 0.  Bitstrings
-- are wire 0 first: the paper's x β y is here insertions into the
-- context of the remaining wires.
--
-- The paper leaves the order of each product unspecified, as it does
-- not matter in its proofs; here it is the binary order of the
-- context.  The paper's composition ∘ of words over P is
-- concatenation in the order written, as is ours.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Encoding where

open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not)
open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ<)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_)
open import Data.List using (List ; [] ; _∷_ ; foldr ; map ; reverse ; upTo ; applyUpTo)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _<ᵇ_ ; _≡ᵇ_ ; _<?_) renaming (_^_ to _^ℕ_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (index ; fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P

import Data.Fin.Properties as FP

------------------------------------------------------------------------
-- Products of words, and the letters of P with their side conditions
-- decided

-- ∏ over a list, in the order of the list.
∏ : {A Y : Set} → List A → (A → Word Y) → Word Y
∏ xs f = foldr (λ a w → f a • w) ε xs

-- A range of wires, increasing and decreasing.
range↑ : ℕ → ℕ → List ℕ          -- from i to j − 1, increasing
range↑ i j = map (i +_) (upTo (j ∸ i))

range↓ : ℕ → ℕ → List ℕ          -- from j − 1 down to i
range↓ i j = reverse (range↑ i j)

------------------------------------------------------------------------
-- Side conditions on four indices, and the transposition of two

-- Four distinct indices.
distinct4 : ℕ → ℕ → ℕ → ℕ → Bool
distinct4 a b c d =
  not (a ≡ᵇ b) ∧ not (a ≡ᵇ c) ∧ not (a ≡ᵇ d) ∧ not (b ≡ᵇ c) ∧ not (b ≡ᵇ d) ∧ not (c ≡ᵇ d)

-- The two smallest naturals not among four given ones, e < f.
private
  free : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ    -- fuel, start
  free zero       v a b c d = v
  free (suc fuel) v a b c d =
    if (v ≡ᵇ a) ∨ (v ≡ᵇ b) ∨ (v ≡ᵇ c) ∨ (v ≡ᵇ d) then free fuel (suc v) a b c d else v

twoSmallest : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
twoSmallest a b c d =
  let e = free 5 0 a b c d in e , free 5 (suc e) a b c d

-- The transposition of k and i, applied to v.
τ : ℕ → ℕ → ℕ → ℕ
τ k i v = if v ≡ᵇ k then i else if v ≡ᵇ i then k else v

module _ {n : ℕ} where
  private
    N = 2 ^ℕ n

  -- The letters, ε when the indices coincide (the words of the paper
  -- never do; deciding it here keeps the definitions free of proofs).
  zz : Fin N → Fin N → Word (GenP n)
  zz a b = [ −1−1 a b ]ʷ

  zx : Fin N → Fin N → Fin N → Word (GenP n)
  zx c a b with a FP.≟ b
  ... | yes _   = ε
  ... | no a≢b  = [ −1X c a b a≢b ]ʷ

  xx : Fin N → Fin N → Fin N → Fin N → Word (GenP n)
  xx a b c d with a FP.≟ b | c FP.≟ d
  ... | no a≢b | no c≢d = [ XX a b c d a≢b c≢d ]ʷ
  ... | _      | _      = ε

  hh : Fin N → Fin N → Fin N → Fin N → Word (GenP n)
  hh a b c d with a FP.≟ b | c FP.≟ d
  ... | no a≢b | no c≢d = [ HH a b c d a≢b c≢d ]ʷ
  ... | _      | _      = ε

  -- The same with natural-number indices, ε when one is out of range.
  toFin : ℕ → Maybe (Fin N)
  toFin k with k <? N
  ... | yes k<N = just (fromℕ< k<N)
  ... | no _    = nothing

  zzℕ : ℕ → ℕ → Word (GenP n)
  zzℕ a b with toFin a | toFin b
  ... | just a′ | just b′ = zz a′ b′
  ... | _       | _       = ε

  zxℕ : ℕ → ℕ → ℕ → Word (GenP n)
  zxℕ c a b with toFin c | toFin a | toFin b
  ... | just c′ | just a′ | just b′ = zx c′ a′ b′
  ... | _       | _       | _       = ε

  xxℕ hhℕ : ℕ → ℕ → ℕ → ℕ → Word (GenP n)
  xxℕ a b c d with toFin a | toFin b | toFin c | toFin d
  ... | just a′ | just b′ | just c′ | just d′ = xx a′ b′ c′ d′
  ... | _       | _       | _       | _       = ε
  hhℕ a b c d with toFin a | toFin b | toFin c | toFin d
  ... | just a′ | just b′ | just c′ | just d′ = hh a′ b′ c′ d′
  ... | _       | _       | _       | _       = ε

  ----------------------------------------------------------------------
  -- The words Σ and Σ′ of Definition E.1 (Appendix E.1)
  --
  -- Products of four (−1)_[m] X_[k,i] letters carrying the basis
  -- vectors 0, 1, 3, 2 to a, b, c, d; each factor is present when its
  -- transposition is not the identity, which is when its two indices
  -- differ — exactly when the letter exists.

  Σ Σ′ : ℕ → ℕ → ℕ → ℕ → Word (GenP n)
  Σ a b c d =
    let m₃ = τ d 2 4
        i₂ = τ d 2 3
        m₂ = τ c i₂ m₃
        i₁ = τ c i₂ (τ d 2 1)
        m₁ = τ b i₁ m₂
        i₀ = τ b i₁ (τ c i₂ (τ d 2 0))
        m₀ = τ a i₀ m₁
    in zxℕ m₀ a i₀ • zxℕ m₁ b i₁ • zxℕ m₂ c i₂ • zxℕ m₃ d 2
  Σ′ a b c d =
    let m₃ = τ d 2 4
        i₂ = τ d 2 3
        m₂ = τ c i₂ m₃
        i₁ = τ c i₂ (τ d 2 1)
        m₁ = τ b i₁ m₂
        i₀ = τ b i₁ (τ c i₂ (τ d 2 0))
    in zxℕ 4 d 2 • zxℕ m₃ c i₂ • zxℕ m₂ b i₁ • zxℕ m₁ a i₀

-- The H-pattern of four codes (the caption of Figure 8, Definition
-- 8.3): b and c are a with one bit flipped each, d is a with both
-- flipped, and a is 0 at both bits.  The result is the wire flipped by
-- b, then the one flipped by c.
hpat : ∀ {n} → Bits n → Bits n → Bits n → Bits n → Maybe (ℕ × ℕ)
hpat a b c d with diff a b | diff a c | diff a d
... | pb ∷ [] | pc ∷ [] | q₁ ∷ q₂ ∷ [] =
      if (((pb ≡ᵇ q₁) ∧ (pc ≡ᵇ q₂)) ∨ ((pb ≡ᵇ q₂) ∧ (pc ≡ᵇ q₁)))
          ∧ not (lookupℕ pb a) ∧ not (lookupℕ pc a)
      then just (pb , pc) else nothing
... | _ | _ | _ = nothing

------------------------------------------------------------------------
-- The position of a gate

data View (n : ℕ) : Set where
  one : ℕ → Gate 1 → View n      -- a one-wire gate, and its wire
  two : ℕ → Gate 2 → View n      -- a two-wire gate, and its lower wire

view : ∀ {n} → Gen n → View n
view (gate₀ ())
view (gate₁ h) = one 0 h
view (gate₂ h) = two 0 h
view (g ↥) with view g
... | one p h = one (suc p) h
... | two p h = two (suc p) h

------------------------------------------------------------------------
-- The encoding, on n = m + 3 wires

module _ {m : ℕ} where
  private
    n : ℕ
    n = ₃₊ m
    idx : Bits n → Fin (2 ^ℕ n)
    idx = index n

  -- The basis vector with the gate bit g on wire p, the pairing bit b
  -- on its pairing wire (the one just below the gate, or the top wire
  -- for a gate on wire 0), and the context c on the other wires.
  str₁ : ℕ → Bits (₁₊ m) → Bool → Bool → Bits n
  str₁ zero    c b g = insertℕ (₂₊ m) b (insertℕ 0 g c)
  str₁ (suc p) c b g = insertℕ (suc p) g (insertℕ p b c)

  -- The same for a two-wire gate on wires p and p + 1, u the bit of the
  -- upper wire (the control of CH) and t of the lower.
  str₂ : ℕ → Bits m → Bool → Bool → Bool → Bits n
  str₂ zero    c b u t = insertℕ (₂₊ m) b (insertℕ 1 u (insertℕ 0 t c))
  str₂ (suc p) c b u t = insertℕ (₂₊ p) u (insertℕ (suc p) t (insertℕ p b c))

  -- Definition 8.2 on the gates: Z and H on wire p, CZ and CH on wires
  -- p and p + 1.
  E-Z E-H : ℕ → Word (GenP n)
  E-Z p = ∏ (allBits (₁₊ m)) λ c →
    zz (idx (str₁ p c false true)) (idx (str₁ p c true true))
  E-H p = ∏ (allBits (₁₊ m)) λ c →
    hh (idx (str₁ p c false false)) (idx (str₁ p c false true))
       (idx (str₁ p c true false))  (idx (str₁ p c true true))

  E-CZ E-CH : ℕ → Word (GenP n)
  E-CZ p = ∏ (allBits m) λ c →
    zz (idx (str₂ p c false true true)) (idx (str₂ p c true true true))
  E-CH p = ∏ (allBits m) λ c →
    hh (idx (str₂ p c false true false)) (idx (str₂ p c false true true))
       (idx (str₂ p c true true false))  (idx (str₂ p c true true true))

  -- The encoding of a generator.
  e : Gen n → Word (GenP n)
  e g with view g
  ... | one p H-gate  = E-H p
  ... | one p Z-gate  = E-Z p
  ... | two p CZ-gate = E-CZ p
  ... | two p CH-gate = E-CH p

  ----------------------------------------------------------------------
  -- The swap and the X gate (Definition 8.2, Appendix A.4.1)

  -- The basis vector with bits u, t on wires p + 1, p and context c.
  str₂′ : ℕ → Bits (₁₊ m) → Bool → Bool → Bits n
  str₂′ p c u t = insertℕ (suc p) u (insertℕ p t c)

  -- With bit g on wire p and context c.
  str₁′ : ℕ → Bits (₂₊ m) → Bool → Bits n
  str₁′ p c g = insertℕ p g c

  -- E_{k,ℓ}(⨉), the swap of wires p and p + 1.
  E-swap : ℕ → Word (GenP n)
  E-swap p =
    E-CZ p •
    ∏ (allBits (₁₊ m)) (λ c → zx (idx (str₂′ p c true true)) (idx (str₂′ p c true false)) (idx (str₂′ p c true true))) •
    ∏ (allBits (₁₊ m)) (λ c → zx (idx (str₂′ p c false true)) (idx (str₂′ p c false true)) (idx (str₂′ p c true true))) •
    ∏ (allBits (₁₊ m)) (λ c → zx (idx (str₂′ p c true true)) (idx (str₂′ p c true false)) (idx (str₂′ p c true true)))

  -- E_{k,ℓ}(⊕), the X gate on wire p, and ℰ, the negation of a control
  -- of the multi-controlled Hadamard: the X gate when the control bit
  -- is 1, nothing when it is 0.  (The paper writes ℰ^{1−x} with ε at
  -- x = 1; Auxiliary.Checks8 decides Equations (36) and (37) on three
  -- qubits, and they hold with the negations on the controls that are
  -- 1 — the rules carry the black controls of the gate to the
  -- all-white H_[0,1] H_[3,2] — and fail at every instance the other
  -- way round.)
  E-X : ℕ → Word (GenP n)
  E-X p = E-Z p • ∏ (allBits (₂₊ m)) λ c →
    zx (idx (str₁′ p c true)) (idx (str₁′ p c false)) (idx (str₁′ p c true))

  ℰ : Bool → ℕ → Word (GenP n)
  ℰ true  p = E-X p
  ℰ false p = ε

  ----------------------------------------------------------------------
  -- The words W₁ and W₂ of Equations (36) and (37)
  --
  -- For H_[a,b] H_[c,d] whose codes are x0y0z, x1y0z, x0y1z, x1y1z (W₁)
  -- or x0y0z, x0y1z, x1y0z, x1y1z (W₂): a swap network carries the two
  -- varying wires, i (lower) and j (upper), down to wires 0 and 1, the
  -- controls keeping their order; X negates the controls that are 1
  -- (see ℰ); then H_[0,1] H_[3,2]; then back.  The paper indexes the
  -- negation of the j-th control from the top as ℰ_{j,n−j−2}: it is the
  -- control on wire n − 1 − j, so the negations run over the wires
  -- 2 … n − 1 of the moved frame, with the bits of the base code a at
  -- the wires other than i and j.

  -- The control bits in the moved frame, wire 2 of the frame first.
  ctrls : Bits n → ℕ → ℕ → Bits (₁₊ m)
  ctrls a i j = removeℕ i (removeℕ j a)

  negations↑ negations↓ : Bits n → ℕ → ℕ → Word (GenP n)
  negations↑ a i j = ∏ (range↑ 2 n) λ w → ℰ (lookupℕ (w ∸ 2) (ctrls a i j)) w
  negations↓ a i j = ∏ (range↓ 2 n) λ w → ℰ (lookupℕ (w ∸ 2) (ctrls a i j)) w

  -- The swap network and its reverse.  Read with the left factor
  -- acting first, swaps← carries wire j down to wire i + 1, one swap
  -- at a time from the top, then the pair down to wires 0 and 1; swaps→
  -- carries them back.  The products over i + 1 … j − 1 run downwards
  -- in swaps← and upwards in swaps→, as the paper's ∏← and ∏→ say: the
  -- other way round they carry wire j only to wire j − 1, which is the
  -- same thing only when j − i < 3 — always on three qubits, where
  -- Checks8 decides these rules, and first wrong on four
  -- (`scratchpad/tW.py`).
  swaps→ swaps← : ℕ → ℕ → Word (GenP n)
  swaps→ i j =
    ∏ (range↑ 0 i) (λ k → E-swap (suc k) • E-swap k) •
    ∏ (range↑ (suc i) j) (λ k → E-swap k)
  swaps← i j =
    ∏ (range↓ (suc i) j) (λ k → E-swap k) •
    ∏ (range↓ 0 i) (λ k → E-swap k • E-swap (suc k))

  -- H_[0,1] H_[3,2] at this width.
  HH₀₁₃₂ : Word (GenP n)
  HH₀₁₃₂ = hh (fin8 {m} ₀) (fin8 {m} ₁) (fin8 {m} ₃) (fin8 {m} ₂)

  W₁ W₂ : Bits n → ℕ → ℕ → Word (GenP n)
  W₁ a i j = swaps← i j • E-swap 0 • negations↑ a i j • HH₀₁₃₂ •
             negations↓ a i j • E-swap 0 • swaps→ i j
  W₂ a i j = swaps← i j • negations↑ a i j • HH₀₁₃₂ • negations↓ a i j • swaps→ i j
