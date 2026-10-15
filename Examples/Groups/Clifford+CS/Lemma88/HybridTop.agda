------------------------------------------------------------------------
-- Presentations of groups
--
-- The hybrid letter at the top pair commutes with every decoded K-free
-- word below it
--
-- The generic reduction of the hybrid rules of P′ (Auxiliary.Rules)
-- carries every hybrid letter to the top pair N − 2, N − 1.  A K-free
-- word whose phased permutation fixes that pair with phase 0 has a
-- normal form (Auxiliary.NF) all of whose letters lie on indices below
-- N − 2, so its decoding is a word in the consecutive letters on pairs
-- j, j + 1 with j + 2 ≤ N − 2, each far from the top pair.  Here: the
-- far facts at the top pair (`TopFar`) give the commutation with any
-- decoded K-free word whose letters have all their indices below N − 2
-- (`comm-word`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (Word ; WRel)

module Examples.Groups.Clifford+CS.Lemma88.HybridTop
  {X : Set} (Γ : WRel X) (N : ℕ) (p p′ l h k : ℕ → Word X) where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (zero ; suc ; _+_ ; _∸_ ; _<_ ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties as NP using ()
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; [_]ʷ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

open PB Γ using (_≈_)

private module FrN = Fr Γ N p p′ l h k

-- The top pair.
top : ℕ
top = N ∸ 2

-- The far facts at the top pair.
record TopFar : Set where
  field
    far-p : ∀ {j} → suc (suc j) ≤ top → k top • p j ≈ p j • k top
    far-l : ∀ {j} → suc (suc j) ≤ top → k top • l j ≈ l j • k top

-- A K-free letter whose indices all lie below the top pair.
LowG : GenP N → Set
LowG (pp a b)         = toℕ a < top × toℕ b < top
LowG (px c a b _)     = toℕ c < top × toℕ a < top × toℕ b < top
LowG (dx a b c e _ _) = toℕ a < top × toℕ b < top × toℕ c < top × toℕ e < top
LowG (ki _ _ _ _)     = ⊥

data LowW : Word (GenP N) → Set where
  gen : ∀ {g} → LowG g → LowW [ g ]ʷ
  nil : LowW ε
  cat : ∀ {u v} → LowW u → LowW v → LowW (u • v)

module Proofs (F : FrN.Facts) (T : TopFar) where

  open FrN.Facts F
  open FrN.Proofs F
  open TopFar T
  open Tools Γ hiding (_≈_)

  private
    kt : Word X
    kt = k top

    -- A letter on the pair j, j + 1 with j + 2 ≤ top is valid.
    v1 : ∀ {j} → suc (suc j) ≤ top → suc j < N
    v1 le = NP.≤-trans le (NP.m∸n≤m N 2)

  -- The consecutive letters below the top pair commute with k top.
  comm-p : ∀ {j} → suc (suc j) ≤ top → Comm (p j) kt
  comm-p le = sym (far-p le)

  comm-l : ∀ {j} → suc (suc j) ≤ top → Comm (l j) kt
  comm-l le = sym (far-l le)

  comm-p′ : ∀ {j} → suc (suc j) ≤ top → Comm (p′ j) kt
  comm-p′ le = comm-inv (p-inv (v1 le)) (p′-inv (v1 le)) (comm-p le)

  comm-h : ∀ {j} → suc (suc j) ≤ top → Comm (h j) kt
  comm-h le = comm-inv (l-inv (v1 le)) (h-inv (v1 le)) (comm-l le)

  -- Chains below the top pair.
  private
    le2 : ∀ {j m} → j < m → m < top → suc (suc j) ≤ top
    le2 jm mt = NP.≤-trans (s≤s jm) mt

  comm-up : ∀ a e → a + e < top → Comm (pp-up a e) kt
  comm-up a e lt = up-commR a e (λ _ je → comm-p (le2 je lt))

  comm-dn : ∀ a e → a + e < top → Comm (pp-dn a e) kt
  comm-dn a e lt = dn-commR a e (λ _ je → comm-p′ (le2 je lt))

  comm-dPP : ∀ {a b} → a < top → b < top → Comm (dPP a b) kt
  comm-dPP {a} {b} la lb with NP.≤-total a b
  ... | inj₁ ab = Eq.subst (λ w → Comm w kt) (Eq.sym (dPP-up ab))
                    (comm-up a (b ∸ a) (Eq.subst (_< top) (Eq.sym (NP.m+[n∸m]≡n ab)) lb))
  ... | inj₂ ba = Eq.subst (λ w → Comm w kt) (Eq.sym (dPP-dn ba))
                    (comm-dn b (a ∸ b) (Eq.subst (_< top) (Eq.sym (NP.m+[n∸m]≡n ba)) la))

  -- The rotation chains from a over e steps, below the top pair.
  comm-dLo : ∀ a e → a + e < top → Comm (dLo a e) kt
  comm-dLo a zero          lt = comm-ε
  comm-dLo a (suc zero)    lt = comm-l (Eq.subst (_≤ top) (Eq.cong suc (NP.+-comm a 1)) lt)
  comm-dLo a (suc (suc e)) lt =
    comm-• (comm-h ha) (comm-• (comm-dLo (suc a) (suc e) lt′) (comm-l ha))
    where
      ha : suc (suc a) ≤ top
      ha = NP.≤-trans (s≤s (s≤s (NP.m≤m+n a (suc e)))) (Eq.subst (_≤ top) (Eq.cong suc (NP.+-suc a (suc e))) lt)
      lt′ : suc a + suc e < top
      lt′ = Eq.subst (_< top) (NP.+-suc a (suc e)) lt

  comm-dHi : ∀ a e → a + e < top → Comm (dHi a e) kt
  comm-dHi a zero          lt = comm-ε
  comm-dHi a (suc zero)    lt = comm-h (Eq.subst (_≤ top) (Eq.cong suc (NP.+-comm a 1)) lt)
  comm-dHi a (suc (suc e)) lt =
    comm-• (comm-h ha) (comm-• (comm-dHi (suc a) (suc e) lt′) (comm-l ha))
    where
      ha : suc (suc a) ≤ top
      ha = NP.≤-trans (s≤s (s≤s (NP.m≤m+n a (suc e)))) (Eq.subst (_≤ top) (Eq.cong suc (NP.+-suc a (suc e))) lt)
      lt′ : suc a + suc e < top
      lt′ = Eq.subst (_< top) (NP.+-suc a (suc e)) lt

  -- The chains of a signed exchange between two indices below the top.
  private
    lo-ab : ∀ a b → b < top → (∀ e → a + e < top → Comm (dLo a e) kt) → Comm (dLo a (b ∸ a)) kt
    lo-ab a b lb c with NP.≤-total a b
    ... | inj₁ ab = c (b ∸ a) (Eq.subst (_< top) (Eq.sym (NP.m+[n∸m]≡n ab)) lb)
    ... | inj₂ ba = Eq.subst (λ e → Comm (dLo a e) kt) (Eq.sym (NP.m≤n⇒m∸n≡0 ba)) comm-ε

    hi-ab : ∀ a b → b < top → Comm (dHi a (b ∸ a)) kt
    hi-ab a b lb with NP.≤-total a b
    ... | inj₁ ab = comm-dHi a (b ∸ a) (Eq.subst (_< top) (Eq.sym (NP.m+[n∸m]≡n ab)) lb)
    ... | inj₂ ba = Eq.subst (λ e → Comm (dHi a e) kt) (Eq.sym (NP.m≤n⇒m∸n≡0 ba)) comm-ε

  comm-dPXs : ∀ x y c a b → c < top → a < top → b < top → Comm (dPXs x y c a b) kt
  comm-dPXs true  _     c a b lc la lb = lo-ab a b lb (comm-dLo a)
  comm-dPXs false true  c a b lc la lb = hi-ab a b lb
  comm-dPXs false false c a b lc la lb =
    comm-• (comm-dPP lc la) (comm-• (comm-dPP lc la) (lo-ab a b lb (comm-dLo a)))

  comm-dPX : ∀ c a b → c < top → a < top → b < top → Comm (dPX c a b) kt
  comm-dPX c a b = comm-dPXs (Data.Nat._≡ᵇ_ c a) (Data.Nat._≡ᵇ_ c b) c a b

  -- Letters and words.
  comm-letter : ∀ g → LowG g → Comm (d g) kt
  comm-letter (pp a b)         (la , lb)            = comm-dPP la lb
  comm-letter (px c a b _)     (lc , la , lb)       = comm-dPX (toℕ c) (toℕ a) (toℕ b) lc la lb
  comm-letter (dx a b c e _ _) (la , lb , lc , le′) =
    comm-• (comm-dPX (toℕ a) (toℕ a) (toℕ b) la la lb) (comm-dPX (toℕ b) (toℕ c) (toℕ e) lb lc le′)
  comm-letter (ki _ _ _ _)     ()

  comm-word : ∀ {w} → LowW w → Comm ((d ʷ) w) kt
  comm-word (gen {g} lg) = comm-letter g lg
  comm-word nil          = comm-ε
  comm-word (cat u v)    = comm-• (comm-word u) (comm-word v)
