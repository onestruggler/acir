------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger step 1: the long relations C1, C10, C11, C14 and C15 are
-- sound for the P4 action, each decided by one boolean
--
-- Each relation lives on the bottom k wires (k = 1, 2, 3) of a circuit
-- of any width.  A word on k wires, widened, acts on the first k entries
-- of a Pauli as it does at width k and leaves the rest alone (`local`),
-- so the relation follows from its 4ᵏ instances at width k, at phase 0
-- (lift-eq restores the phase).  Those are one boolean, `agree`, which
-- Eq.refl decides by evaluation, and `every` reads off each instance.
--
-- Evaluating a boolean is one reduction, in which the action of each
-- letter is computed once.  The earlier proofs compared the two actions
-- by Eq.refl, one Pauli at a time, and the conversion checker, which
-- reduces each component of a result separately, recomputed the
-- actions of the prefixes for each component: 24 letters took 40 ms,
-- 48 took 3.6 s, and Soundness, which held them, 344 s.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Selinger.LongRelations where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≡ᵇ_)
import Data.Nat.Base as ℕ
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using ([] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap)

-- The prime from the module the action takes it from (see Soundness).
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg)
import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic
  using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate
        ; S ; H ; CZ ; ⊤⊥ ; ⊥⊤ ; _↥ ; _↑ ; _↓)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli)
open import Examples.Groups.Pauli.Qubit.SignedPauli using (Φ ; P4Carrier)
open import Examples.Groups.ProjectiveClifford.Qubit.CliffordAction using (cact ; cact1 ; δ)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Action using (lift-eq)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- The words

-- The scalar and its friends as symplectic words.
SH : Word (Gen (₁₊ n))
SH = S • H

ω : Word (Gen (₁₊ n))
ω = SH ^ 3

ω⁻¹ : Word (Gen (₁₊ n))
ω⁻¹ = ω ^ 7

-- The relations' words, named.
private

  L10 R10 L11 R11 : Word (Gen (₂₊ n))
  L10 = CZ • H ↑ • CZ
  R10 = SH ↑ • CZ • (S • H • S) ↑ • S ↓ • ω⁻¹
  L11 = CZ • H ↓ • CZ
  R11 = SH ↓ • CZ • (S • H • S) ↓ • S ↑ • ω⁻¹

  W1 : Word (Gen (₁₊ n))
  W1 = ω ^ 8

  W14 W15 : Word (Gen (₃₊ n))
  W14 = (⊤⊥ ↑ • CZ ↓) ^ 3
  W15 = (⊥⊤ ↓ • CZ ↑) ^ 3

------------------------------------------------------------------------
-- A word on k wires, widened by n idle wires on top

private

  widen : Gen k → Gen (k ℕ.+ n)
  widen (gate₁ h) = gate₁ h
  widen (gate₂ h) = gate₂ h
  widen (g ↥)     = widen g ↥

  ext : P4Carrier k → Pauli n → P4Carrier (k ℕ.+ n)
  ext x ps = proj₁ x , proj₂ x ++ ps

  δ-widen : (g : Gen k) (P : Pauli k) (ps : Pauli n) → δ (widen g) (P ++ ps) ≡ δ g P
  δ-widen (gate₁ H-gate)  (p ∷ P)      ps = Eq.refl
  δ-widen (gate₁ S-gate)  (p ∷ P)      ps = Eq.refl
  δ-widen (gate₂ CZ-gate) (p ∷ p′ ∷ P) ps = Eq.refl
  δ-widen (g ↥)           (p ∷ P)      ps = δ-widen g P ps

  actg-widen : (g : Gen k) (P : Pauli k) (ps : Pauli n) → actg (widen g) (P ++ ps) ≡ actg g P ++ ps
  actg-widen (gate₁ H-gate)  (p ∷ P)      ps = Eq.refl
  actg-widen (gate₁ S-gate)  (p ∷ P)      ps = Eq.refl
  actg-widen (gate₂ CZ-gate) (p ∷ p′ ∷ P) ps = Eq.refl
  actg-widen (g ↥)           (p ∷ P)      ps = Eq.cong (p ∷_) (actg-widen g P ps)

  local1 : (g : Gen k) (x : P4Carrier k) (ps : Pauli n) → cact1 (widen g) (ext x ps) ≡ ext (cact1 g x) ps
  local1 g (s , P) ps = Eq.cong₂ (λ d Q → s + d , Q) (δ-widen g P ps) (actg-widen g P ps)

  -- The widened word acts as the word, on the first k entries.
  local : (w : Word (Gen k)) (x : P4Carrier k) (ps : Pauli n) →
          cact (wmap widen w) (ext x ps) ≡ ext (cact w x) ps
  local [ g ]ʷ  x ps = local1 g x ps
  local ε       x ps = Eq.refl
  local (u • v) x ps = Eq.trans (Eq.cong (cact (wmap widen u)) (local v x ps)) (local u (cact v x) ps)

------------------------------------------------------------------------
-- Deciding the instances at width k

private

  eqF : {m : ℕ} → Fin m → Fin m → Bool
  eqF a b = toℕ a ≡ᵇ toℕ b

  eqP : Pauli k → Pauli k → Bool
  eqP []             []               = true
  eqP ((a , b) ∷ P)  ((a′ , b′) ∷ Q)  = eqF a a′ ∧ eqF b b′ ∧ eqP P Q

  eqC : P4Carrier k → P4Carrier k → Bool
  eqC (s , P) (s′ , Q) = eqF s s′ ∧ eqP P Q

  T-∧₁ : (x y : Bool) → T (x ∧ y) → T x
  T-∧₁ true y t = tt

  T-∧₂ : (x y : Bool) → T (x ∧ y) → T y
  T-∧₂ true y t = t

  eqF-sound : {m : ℕ} (a b : Fin m) → T (eqF a b) → a ≡ b
  eqF-sound a b t = toℕ-injective (≡ᵇ⇒≡ (toℕ a) (toℕ b) t)

  eqP-sound : (P Q : Pauli k) → T (eqP P Q) → P ≡ Q
  eqP-sound []            []              t = Eq.refl
  eqP-sound ((a , b) ∷ P) ((a′ , b′) ∷ Q) t =
    Eq.cong₂ _∷_ (Eq.cong₂ _,_ (eqF-sound a a′ (T-∧₁ x (y ∧ z) t)) (eqF-sound b b′ (T-∧₁ y z t′)))
                 (eqP-sound P Q (T-∧₂ y z t′))
    where
    x = eqF a a′
    y = eqF b b′
    z = eqP P Q
    t′ = T-∧₂ x (y ∧ z) t

  eqC-sound : (x y : P4Carrier k) → T (eqC x y) → x ≡ y
  eqC-sound (s , P) (s′ , Q) t =
    Eq.cong₂ _,_ (eqF-sound s s′ (T-∧₁ (eqF s s′) (eqP P Q) t)) (eqP-sound P Q (T-∧₂ (eqF s s′) (eqP P Q) t))

  -- A predicate holds of every Pauli on k wires.
  all : (k : ℕ) → (Pauli k → Bool) → Bool
  all zero    f = f []
  all (suc k) f = all k (λ P → f ((₀ , ₀) ∷ P)) ∧ all k (λ P → f ((₀ , ₁) ∷ P))
                ∧ all k (λ P → f ((₁ , ₀) ∷ P)) ∧ all k (λ P → f ((₁ , ₁) ∷ P))

  every : (k : ℕ) (f : Pauli k → Bool) → T (all k f) → (P : Pauli k) → T (f P)
  every zero    f t [] = t
  every (suc k) f t ((a , b) ∷ P) = pick a b
    where
    f₀₀ f₀₁ f₁₀ f₁₁ : Pauli k → Bool
    f₀₀ Q = f ((₀ , ₀) ∷ Q)
    f₀₁ Q = f ((₀ , ₁) ∷ Q)
    f₁₀ Q = f ((₁ , ₀) ∷ Q)
    f₁₁ Q = f ((₁ , ₁) ∷ Q)
    t₁ = T-∧₂ (all k f₀₀) (all k f₀₁ ∧ all k f₁₀ ∧ all k f₁₁) t
    t₂ = T-∧₂ (all k f₀₁) (all k f₁₀ ∧ all k f₁₁) t₁
    pick : (a b : ℤ ₚ) → T (f ((a , b) ∷ P))
    pick ₀ ₀ = every k f₀₀ (T-∧₁ (all k f₀₀) (all k f₀₁ ∧ all k f₁₀ ∧ all k f₁₁) t) P
    pick ₀ ₁ = every k f₀₁ (T-∧₁ (all k f₀₁) (all k f₁₀ ∧ all k f₁₁) t₁) P
    pick ₁ ₀ = every k f₁₀ (T-∧₁ (all k f₁₀) (all k f₁₁) t₂) P
    pick ₁ ₁ = every k f₁₁ (T-∧₂ (all k f₁₀) (all k f₁₁) t₂) P

  -- The two words agree at phase 0 on every Pauli on k wires.
  agree : (k : ℕ) → Word (Gen k) → Word (Gen k) → Bool
  agree k u v = all k (λ P → eqC (cact u (₀ , P)) (cact v (₀ , P)))

  -- The relation on the bottom k wires, from the instances at width k.
  -- The widened words, and the Pauli split at k, are given with
  -- equations checked by Eq.refl, so that they are compared as words and
  -- vectors and never through the action.
  by-local : (u v : Word (Gen k)) (u′ v′ : Word (Gen (k ℕ.+ n))) →
             wmap widen u ≡ u′ → wmap widen v ≡ v′ → T (agree k u v) →
             (s : Φ) (P : Pauli k) (ps : Pauli n) (P′ : Pauli (k ℕ.+ n)) → P ++ ps ≡ P′ →
             cact u′ (s , P′) ≡ cact v′ (s , P′)
  by-local {k} u v _ _ Eq.refl Eq.refl t s P ps _ Eq.refl = lift-eq (wmap widen u) (wmap widen v) s (P ++ ps)
    (Eq.trans (local u (₀ , P) ps)
      (Eq.trans (Eq.cong (λ x → ext x ps) (eqC-sound _ _ (every k _ t P)))
        (Eq.sym (local v (₀ , P) ps))))

  -- The same at each arity, stated at width ₁₊ n, ₂₊ n, ₃₊ n.  Their
  -- uses then have the goal's type on the nose: at width k ℕ.+ n the
  -- hidden width of cact would differ from the goal's, and comparing the
  -- two would evaluate the action on a symbolic Pauli.
  by-local₁ : (u v : Word (Gen 1)) (u′ v′ : Word (Gen (₁₊ n))) →
              wmap widen u ≡ u′ → wmap widen v ≡ v′ → T (agree 1 u v) →
              (s : Φ) (p : ℤ ₚ × ℤ ₚ) (ps : Pauli n) →
              cact u′ (s , p ∷ ps) ≡ cact v′ (s , p ∷ ps)
  by-local₁ u v u′ v′ eu ev t s p ps = by-local u v u′ v′ eu ev t s (p ∷ []) ps (p ∷ ps) Eq.refl

  by-local₂ : (u v : Word (Gen 2)) (u′ v′ : Word (Gen (₂₊ n))) →
              wmap widen u ≡ u′ → wmap widen v ≡ v′ → T (agree 2 u v) →
              (s : Φ) (p p′ : ℤ ₚ × ℤ ₚ) (ps : Pauli n) →
              cact u′ (s , p ∷ p′ ∷ ps) ≡ cact v′ (s , p ∷ p′ ∷ ps)
  by-local₂ u v u′ v′ eu ev t s p p′ ps =
    by-local u v u′ v′ eu ev t s (p ∷ p′ ∷ []) ps (p ∷ p′ ∷ ps) Eq.refl

  by-local₃ : (u v : Word (Gen 3)) (u′ v′ : Word (Gen (₃₊ n))) →
              wmap widen u ≡ u′ → wmap widen v ≡ v′ → T (agree 3 u v) →
              (s : Φ) (p p′ p″ : ℤ ₚ × ℤ ₚ) (ps : Pauli n) →
              cact u′ (s , p ∷ p′ ∷ p″ ∷ ps) ≡ cact v′ (s , p ∷ p′ ∷ p″ ∷ ps)
  by-local₃ u v u′ v′ eu ev t s p p′ p″ ps =
    by-local u v u′ v′ eu ev t s (p ∷ p′ ∷ p″ ∷ []) ps (p ∷ p′ ∷ p″ ∷ ps) Eq.refl

------------------------------------------------------------------------
-- The relations

c1-sound' : (x : P4Carrier (₁₊ n)) → cact W1 x ≡ cact ε x
c1-sound' (s , p ∷ ps) = by-local₁ W1 ε W1 ε Eq.refl Eq.refl tt s p ps

c10-sound : (x : P4Carrier (₂₊ n)) → cact L10 x ≡ cact R10 x
c10-sound (s , p ∷ p′ ∷ ps) = by-local₂ L10 R10 L10 R10 Eq.refl Eq.refl tt s p p′ ps

c11-sound : (x : P4Carrier (₂₊ n)) → cact L11 x ≡ cact R11 x
c11-sound (s , p ∷ p′ ∷ ps) = by-local₂ L11 R11 L11 R11 Eq.refl Eq.refl tt s p p′ ps

c14-sound : (x : P4Carrier (₃₊ n)) → cact W14 x ≡ cact ε x
c14-sound (s , p ∷ p′ ∷ p″ ∷ ps) = by-local₃ W14 ε W14 ε Eq.refl Eq.refl tt s p p′ p″ ps

c15-sound : (x : P4Carrier (₃₊ n)) → cact W15 x ≡ cact ε x
c15-sound (s , p ∷ p′ ∷ p″ ∷ ps) = by-local₃ W15 ε W15 ε Eq.refl Eq.refl tt s p p′ p″ ps
