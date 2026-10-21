------------------------------------------------------------------------
-- Presentations of groups
--
-- A Hadamard-free letter of P decodes to a word in a few atoms
--
-- Definition 8.3 builds D(p) for a sign pair or a signed exchange by
-- recursion from three families of multi-controlled gates — the box
-- `dZZ₁ a` and the two signed exchanges `dZXlo₁ a`, `dZXhi₁ a` for a
-- and a + 1 — and D(X_[a,b] X_[c,d]) from two signed exchanges.  Here
-- the same recursions are run on names of those gates (`Atom`, the
-- skeleton `skP`), and the decoding of a Hadamard-free word is the
-- skeleton with every name replaced by its gate (`sk-word`), on any
-- number of wires.  DecodingChecks.Base reads each atom once on three
-- wires and decides the decoded letters on products of their matrices.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.Atoms where

open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _<ᵇ_ ; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Decoding

------------------------------------------------------------------------
-- The names of the atoms, and the skeletons

data Atom : Set where
  zA loA hiA : ℕ → Atom

-- A word reversed.
revA : Word Atom → Word Atom
revA [ x ]ʷ   = [ x ]ʷ
revA ε        = ε
revA (s • t)  = revA t • revA s

-- Definition 8.3's recursions on names.
skZZ-chain : ℕ → ℕ → Word Atom
skZZ-chain a zero    = ε
skZZ-chain a (suc d) = [ zA a ]ʷ • skZZ-chain (suc a) d

skZZ : ℕ → ℕ → Word Atom
skZZ a b = if a <ᵇ b then skZZ-chain a (b ∸ a) else skZZ-chain b (a ∸ b)

skZXlo skZXhi : ℕ → ℕ → Word Atom
skZXlo a zero          = ε
skZXlo a (suc zero)    = [ loA a ]ʷ
skZXlo a (suc (suc d)) =
  if parity d
  then [ loA a ]ʷ • skZXlo (suc a) (suc d) • [ hiA a ]ʷ
  else [ hiA (a + suc d) ]ʷ • skZXlo a (suc d) • [ loA (a + suc d) ]ʷ
skZXhi a zero          = ε
skZXhi a (suc zero)    = [ hiA a ]ʷ
skZXhi a (suc (suc d)) =
  if parity d
  then [ loA a ]ʷ • skZXhi (suc a) (suc d) • [ hiA a ]ʷ
  else [ hiA (a + suc d) ]ʷ • skZXhi a (suc d) • [ loA (a + suc d) ]ʷ

skZXself : ℕ → ℕ → Word Atom
skZXself a b = if a <ᵇ b then skZXlo a (b ∸ a) else skZXhi b (a ∸ b)

skZXs : Bool → Bool → ℕ → ℕ → ℕ → ℕ → ℕ → Word Atom
skZXs true  _     lo hi a b c = skZXlo lo (hi ∸ lo)
skZXs false true  lo hi a b c = skZXhi lo (hi ∸ lo)
skZXs false false lo hi a b c = skZXself a b • skZZ c a

skZXb : Bool → ℕ → ℕ → ℕ → Word Atom
skZXb β c a b =
  skZXs (c ≡ᵇ (if β then a else b)) (c ≡ᵇ (if β then b else a))
        (if β then a else b) (if β then b else a) a b c

skZX : ℕ → ℕ → ℕ → Word Atom
skZX c a b = skZXb (a <ᵇ b) c a b

skXX : ℕ → ℕ → ℕ → ℕ → Word Atom
skXX a b c d = skZX b c d • skZX a a b

------------------------------------------------------------------------
-- The skeletons spell the decoding

module _ {m : ℕ} where
  private
    n : ℕ
    n = ₃₊ m

  -- An atom's gate, and the same reversed (as `d` reverses).
  atom : Atom → Circuit n
  atom (zA a)  = dZZ₁ a
  atom (loA a) = dZXlo₁ a
  atom (hiA a) = dZXhi₁ a

  atomR : Atom → Circuit n
  atomR x = rev (atom x)

  -- Whether a letter or a word has no Hadamard pair, and its skeleton.
  hfP : GenP n → Bool
  hfP (HH _ _ _ _ _ _) = false
  hfP _                = true

  hf : Word (GenP n) → Bool
  hf [ p ]ʷ  = hfP p
  hf ε       = true
  hf (u • v) = hf u ∧ hf v

  skP : GenP n → Word Atom
  skP (−1−1 a b)        = revA (skZZ (toℕ a) (toℕ b))
  skP (−1X c a b _)     = revA (skZX (toℕ c) (toℕ a) (toℕ b))
  skP (XX a b c d _ _)  = revA (skXX (toℕ a) (toℕ b) (toℕ c) (toℕ d))
  skP (HH _ _ _ _ _ _)  = ε

  skW : Word (GenP n) → Word Atom
  skW [ p ]ʷ  = skP p
  skW ε       = ε
  skW (u • v) = skW u • skW v

  private
    ifʷ : ∀ (b : Bool) (x y : Word Atom) {x′ y′ : Circuit n} →
          (atom ʷ) x ≡ x′ → (atom ʷ) y ≡ y′ →
          (atom ʷ) (if b then x else y) ≡ (if b then x′ else y′)
    ifʷ true  x y ex ey = ex
    ifʷ false x y ex ey = ey

    -- A word between two atoms.
    mid : ∀ (x z : Atom) (y : Word Atom) {y′ : Circuit n} → (atom ʷ) y ≡ y′ →
          (atom ʷ) ([ x ]ʷ • y • [ z ]ʷ) ≡ atom x • y′ • atom z
    mid x z y e = Eq.cong (λ t → atom x • t • atom z) e

  ex-chain : ∀ a d → (atom ʷ) (skZZ-chain a d) ≡ dZZ-chain a d
  ex-chain a zero    = Eq.refl
  ex-chain a (suc d) = Eq.cong₂ _•_ Eq.refl (ex-chain (suc a) d)

  ex-ZZ : ∀ a b → (atom ʷ) (skZZ a b) ≡ dZZ a b
  ex-ZZ a b = ifʷ (a <ᵇ b) (skZZ-chain a (b ∸ a)) (skZZ-chain b (a ∸ b))
                 (ex-chain a (b ∸ a)) (ex-chain b (a ∸ b))

  ex-lo : ∀ a d → (atom ʷ) (skZXlo a d) ≡ dZXlo a d
  ex-lo a zero          = Eq.refl
  ex-lo a (suc zero)    = Eq.refl
  ex-lo a (suc (suc d)) =
    ifʷ (parity d) ([ loA a ]ʷ • skZXlo (suc a) (suc d) • [ hiA a ]ʷ)
                   ([ hiA (a + suc d) ]ʷ • skZXlo a (suc d) • [ loA (a + suc d) ]ʷ)
                   (mid (loA a) (hiA a) (skZXlo (suc a) (suc d)) (ex-lo (suc a) (suc d)))
                   (mid (hiA (a + suc d)) (loA (a + suc d)) (skZXlo a (suc d)) (ex-lo a (suc d)))

  ex-hi : ∀ a d → (atom ʷ) (skZXhi a d) ≡ dZXhi a d
  ex-hi a zero          = Eq.refl
  ex-hi a (suc zero)    = Eq.refl
  ex-hi a (suc (suc d)) =
    ifʷ (parity d) ([ loA a ]ʷ • skZXhi (suc a) (suc d) • [ hiA a ]ʷ)
                   ([ hiA (a + suc d) ]ʷ • skZXhi a (suc d) • [ loA (a + suc d) ]ʷ)
                   (mid (loA a) (hiA a) (skZXhi (suc a) (suc d)) (ex-hi (suc a) (suc d)))
                   (mid (hiA (a + suc d)) (loA (a + suc d)) (skZXhi a (suc d)) (ex-hi a (suc d)))

  ex-self : ∀ a b → (atom ʷ) (skZXself a b) ≡ dZXself a b
  ex-self a b = ifʷ (a <ᵇ b) (skZXlo a (b ∸ a)) (skZXhi b (a ∸ b))
                   (ex-lo a (b ∸ a)) (ex-hi b (a ∸ b))

  ex-s : ∀ t₁ t₂ lo hi a b c → (atom ʷ) (skZXs t₁ t₂ lo hi a b c) ≡ dZXs t₁ t₂ lo hi a b c
  ex-s true  _     lo hi a b c = ex-lo lo (hi ∸ lo)
  ex-s false true  lo hi a b c = ex-hi lo (hi ∸ lo)
  ex-s false false lo hi a b c = Eq.cong₂ _•_ (ex-self a b) (ex-ZZ c a)

  ex-ZX : ∀ c a b → (atom ʷ) (skZX c a b) ≡ dZX c a b
  ex-ZX c a b =
    ex-s (c ≡ᵇ (if a <ᵇ b then a else b)) (c ≡ᵇ (if a <ᵇ b then b else a))
         (if a <ᵇ b then a else b) (if a <ᵇ b then b else a) a b c

  ex-XX : ∀ a b c d → (atom ʷ) (skXX a b c d) ≡ dXX a b c d
  ex-XX a b c d = Eq.cong₂ _•_ (ex-ZX b c d) (ex-ZX a a b)

  -- Reversing a word of gates is reversing the names.
  rev-ʷ : ∀ s → rev ((atom ʷ) s) ≡ (atomR ʷ) (revA s)
  rev-ʷ [ x ]ʷ  = Eq.refl
  rev-ʷ ε       = Eq.refl
  rev-ʷ (s • t) = Eq.cong₂ _•_ (rev-ʷ t) (rev-ʷ s)

  private
    via : ∀ {s : Word Atom} {w : Circuit n} → (atom ʷ) s ≡ w → rev w ≡ (atomR ʷ) (revA s)
    via {s} e = Eq.trans (Eq.cong rev (Eq.sym e)) (rev-ʷ s)

  -- The decoding of a Hadamard-free letter, and of a Hadamard-free word.
  sk-letter : ∀ (p : GenP n) → hfP p ≡ true → d p ≡ (atomR ʷ) (skP p)
  sk-letter (−1−1 a b)       _ = via {skZZ (toℕ a) (toℕ b)} (ex-ZZ (toℕ a) (toℕ b))
  sk-letter (−1X c a b _)    _ = via {skZX (toℕ c) (toℕ a) (toℕ b)} (ex-ZX (toℕ c) (toℕ a) (toℕ b))
  sk-letter (XX a b c d _ _) _ = via {skXX (toℕ a) (toℕ b) (toℕ c) (toℕ d)} (ex-XX (toℕ a) (toℕ b) (toℕ c) (toℕ d))

  private
    ∧-l : ∀ {x y : Bool} → x ∧ y ≡ true → x ≡ true
    ∧-l {true} _ = Eq.refl

    ∧-r : ∀ {x y : Bool} → x ∧ y ≡ true → y ≡ true
    ∧-r {true} h = h

  sk-word : ∀ (u : Word (GenP n)) → hf u ≡ true → (d ʷ) u ≡ (atomR ʷ) (skW u)
  sk-word [ p ]ʷ  h = sk-letter p h
  sk-word ε       h = Eq.refl
  sk-word (u • v) h = Eq.cong₂ _•_ (sk-word u (∧-l {hf u} h)) (sk-word v (∧-r {hf u} h))
