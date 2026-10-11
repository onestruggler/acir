------------------------------------------------------------------------
-- Presentations of groups
--
-- The Gray code (Clément, Definition 8.1): basis indices as bitstrings
--
-- Section 8 indexes the 2ⁿ basis vectors of n qubits by the binary-
-- reflected Gray code, so that consecutive indices differ in one bit.
-- Bitstrings are the `Bits n` of the semantics, wire 0 first; the
-- paper writes its strings top wire first, so its x β y (x the k top
-- bits, y the bottom ones) is here y ++ β ∷ x.
--
-- The code is given by its bitwise formula, g i = b i xor b (i + 1)
-- for b the binary digits, the standard closed form of the reflected
-- code of Definition 8.1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Gray where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Bool.Properties using (not-involutive)
open import Data.Fin using (Fin ; toℕ ; fromℕ< ; inject≤)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ< ; toℕ-injective)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _<_ ; _≤_ ; s≤s ; z≤n ; _^_)
open import Data.Nat.Properties as NP
  using (+-suc ; +-assoc ; +-comm ; *-suc ; m≤n+m ; +-monoˡ-< ; *-monoʳ-≤ ; ≤-trans ; <-≤-trans)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Binary digits, least significant first

parity : ℕ → Bool
parity zero    = false
parity (suc k) = not (parity k)

half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc k)) = suc (half k)

bit : Bool → ℕ
bit true  = 1
bit false = 0

toBits : (n : ℕ) → ℕ → Bits n
toBits zero    k = []
toBits (suc n) k = parity k ∷ toBits n (half k)

fromBits : Bits n → ℕ
fromBits []       = 0
fromBits (b ∷ bs) = bit b + 2 * fromBits bs

private
  -- Two more is two more.
  two-more : ∀ b m → bit b + 2 * suc m ≡ suc (suc (bit b + 2 * m))
  two-more b m = begin
    bit b + 2 * suc m       ≡⟨ Eq.cong (bit b +_) (*-suc 2 m) ⟩
    bit b + (2 + 2 * m)     ≡⟨ Eq.sym (+-assoc (bit b) 2 (2 * m)) ⟩
    (bit b + 2) + 2 * m     ≡⟨ Eq.cong (_+ 2 * m) (+-comm (bit b) 2) ⟩
    (2 + bit b) + 2 * m     ≡⟨ +-assoc 2 (bit b) (2 * m) ⟩
    2 + (bit b + 2 * m)     ∎
    where open Eq.≡-Reasoning

  -- k = bit (parity k) + 2 · half k.
  split : ∀ k → k ≡ bit (parity k) + 2 * half k
  split zero          = Eq.refl
  split (suc zero)    = Eq.refl
  split (suc (suc k)) = begin
    suc (suc k)
      ≡⟨ Eq.cong (λ v → suc (suc v)) (split k) ⟩
    suc (suc (bit (parity k) + 2 * half k))
      ≡⟨ Eq.sym (two-more (parity k) (half k)) ⟩
    bit (parity k) + 2 * suc (half k)
      ≡⟨ Eq.cong (λ v → bit v + 2 * suc (half k)) (Eq.sym (not-involutive (parity k))) ⟩
    bit (not (not (parity k))) + 2 * suc (half k) ∎
    where open Eq.≡-Reasoning

  parity-bit : ∀ b m → parity (bit b + 2 * m) ≡ b
  parity-bit true  zero    = Eq.refl
  parity-bit false zero    = Eq.refl
  parity-bit b     (suc m) = begin
    parity (bit b + 2 * suc m)              ≡⟨ Eq.cong parity (two-more b m) ⟩
    not (not (parity (bit b + 2 * m)))      ≡⟨ not-involutive _ ⟩
    parity (bit b + 2 * m)                  ≡⟨ parity-bit b m ⟩
    b ∎
    where open Eq.≡-Reasoning

  half-bit : ∀ b m → half (bit b + 2 * m) ≡ m
  half-bit true  zero    = Eq.refl
  half-bit false zero    = Eq.refl
  half-bit b     (suc m) = begin
    half (bit b + 2 * suc m)         ≡⟨ Eq.cong half (two-more b m) ⟩
    suc (half (bit b + 2 * m))       ≡⟨ Eq.cong suc (half-bit b m) ⟩
    suc m ∎
    where open Eq.≡-Reasoning

  -- half k < m when k < 2 m.
  half-< : ∀ k m → k < 2 * m → half k < m
  half-< k m k<2m = NP.*-cancelˡ-< 2 (half k) m
    (NP.≤-<-trans (m≤n+m (2 * half k) (bit (parity k)))
      (Eq.subst (_< 2 * m) (split k) k<2m))

toBits-fromBits : (bs : Bits n) → toBits n (fromBits bs) ≡ bs
toBits-fromBits []       = Eq.refl
toBits-fromBits (b ∷ bs) =
  Eq.cong₂ _∷_ (parity-bit b (fromBits bs))
    (Eq.trans (Eq.cong (toBits _) (half-bit b (fromBits bs))) (toBits-fromBits bs))

fromBits-toBits : ∀ n k → k < 2 ^ n → fromBits (toBits n k) ≡ k
fromBits-toBits zero    zero    _   = Eq.refl
fromBits-toBits zero    (suc k) (s≤s ())
fromBits-toBits (suc n) k       k<n = begin
  bit (parity k) + 2 * fromBits (toBits n (half k))
    ≡⟨ Eq.cong (λ v → bit (parity k) + 2 * v) (fromBits-toBits n (half k) (half-< k (2 ^ n) k<n)) ⟩
  bit (parity k) + 2 * half k
    ≡⟨ Eq.sym (split k) ⟩
  k ∎
  where open Eq.≡-Reasoning

fromBits<2^n : (bs : Bits n) → fromBits bs < 2 ^ n
fromBits<2^n []       = s≤s z≤n
fromBits<2^n (b ∷ bs) =
  <-≤-trans (Eq.subst (bit b + 2 * fromBits bs <_) (Eq.sym (*-suc 2 (fromBits bs)))
                      (+-monoˡ-< (2 * fromBits bs) (bit<2 b)))
            (*-monoʳ-≤ 2 (fromBits<2^n bs))
  where
  bit<2 : ∀ b → bit b < 2
  bit<2 true  = s≤s (s≤s z≤n)
  bit<2 false = s≤s z≤n

------------------------------------------------------------------------
-- The Gray code, as a bijection of bitstrings

hd : Bits n → Bool
hd []      = false
hd (b ∷ _) = b

-- From binary digits to the code and back: g i = b i xor b (i + 1).
gray ungray : Bits n → Bits n
gray []       = []
gray (b ∷ bs) = (b xor hd bs) ∷ gray bs
ungray []       = []
ungray (g ∷ gs) = (g xor hd (ungray gs)) ∷ ungray gs

private
  xor-cancel : ∀ b c → (b xor c) xor c ≡ b
  xor-cancel true  true  = Eq.refl
  xor-cancel true  false = Eq.refl
  xor-cancel false true  = Eq.refl
  xor-cancel false false = Eq.refl

ungray-gray : (bs : Bits n) → ungray (gray bs) ≡ bs
ungray-gray []       = Eq.refl
ungray-gray (b ∷ bs) =
  Eq.cong₂ _∷_
    (Eq.trans (Eq.cong (λ v → (b xor hd bs) xor hd v) (ungray-gray bs)) (xor-cancel b (hd bs)))
    (ungray-gray bs)

gray-ungray : (gs : Bits n) → gray (ungray gs) ≡ gs
gray-ungray []       = Eq.refl
gray-ungray (g ∷ gs) = Eq.cong₂ _∷_ (xor-cancel g (hd (ungray gs))) (gray-ungray gs)

------------------------------------------------------------------------
-- The code of an index, and the index of a code

-- G_n, and G_n⁻¹.  The width is explicit: it cannot be recovered from
-- Fin (2 ^ n) by unification.
code : (n : ℕ) → Fin (2 ^ n) → Bits n
code n a = gray (toBits n (toℕ a))

index : (n : ℕ) → Bits n → Fin (2 ^ n)
index n g = fromℕ< (fromBits<2^n (ungray g))

code-index : ∀ n (g : Bits n) → code n (index n g) ≡ g
code-index n g = begin
  gray (toBits n (toℕ (fromℕ< (fromBits<2^n (ungray g)))))
    ≡⟨ Eq.cong (λ v → gray (toBits n v)) (toℕ-fromℕ< (fromBits<2^n (ungray g))) ⟩
  gray (toBits n (fromBits (ungray g)))
    ≡⟨ Eq.cong gray (toBits-fromBits (ungray g)) ⟩
  gray (ungray g)
    ≡⟨ gray-ungray g ⟩
  g ∎
  where open Eq.≡-Reasoning

index-code : ∀ n (a : Fin (2 ^ n)) → index n (code n a) ≡ a
index-code n a = toℕ-injective (begin
  toℕ (fromℕ< (fromBits<2^n (ungray (code n a))))
    ≡⟨ toℕ-fromℕ< (fromBits<2^n (ungray (code n a))) ⟩
  fromBits (ungray (gray (toBits n (toℕ a))))
    ≡⟨ Eq.cong fromBits (ungray-gray (toBits n (toℕ a))) ⟩
  fromBits (toBits n (toℕ a))
    ≡⟨ fromBits-toBits n (toℕ a) (toℕ<n a) ⟩
  toℕ a ∎)
  where open Eq.≡-Reasoning

code-injective : ∀ n {a b : Fin (2 ^ n)} → code n a ≡ code n b → a ≡ b
code-injective n {a} {b} e =
  Eq.trans (Eq.sym (index-code n a)) (Eq.trans (Eq.cong (index n) e) (index-code n b))

index-injective : ∀ n {g h : Bits n} → index n g ≡ index n h → g ≡ h
index-injective n {g} {h} e =
  Eq.trans (Eq.sym (code-index n g)) (Eq.trans (Eq.cong (code n) e) (code-index n h))

------------------------------------------------------------------------
-- Small indices at width n ≥ 3

private
  1≤2^ : ∀ m → 1 ≤ 2 ^ m
  1≤2^ zero    = NP.≤-refl
  1≤2^ (suc m) = ≤-trans (1≤2^ m) (NP.m≤m+n (2 ^ m) (1 * 2 ^ m))

8≤2^ : ∀ m → 8 ≤ 2 ^ (suc (suc (suc m)))
8≤2^ m = *-monoʳ-≤ 2 (*-monoʳ-≤ 2 (*-monoʳ-≤ 2 (1≤2^ m)))

-- The indices 0 … 7 as basis indices on m + 3 qubits.
fin8 : ∀ {m} → Fin 8 → Fin (2 ^ (suc (suc (suc m))))
fin8 {m} i = inject≤ i (8≤2^ m)
