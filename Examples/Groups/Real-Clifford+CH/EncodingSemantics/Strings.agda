------------------------------------------------------------------------
-- Presentations of groups
--
-- The basis vectors of the encoding (Definition 8.2): a gate's wire,
-- its pairing wire, and the context of the other wires, with the
-- correspondence between a basis vector and its context
--
-- Encoding builds the basis vectors str₁ p c b g (a one-wire gate on
-- wire p, its pairing bit b, the context c on the other wires) and
-- str₂ p c b u t (a two-wire gate on wires p and p + 1).  Here the
-- context and the pairing bit are read back off a basis vector, and
-- the two directions are shown inverse: this is what lets a product
-- over all contexts be evaluated at a basis vector.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.EncodingSemantics.Strings where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; n≤1+n ; ≤-trans ; ≤-pred)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
open import Examples.Groups.Real-Clifford+CH.Encoding

------------------------------------------------------------------------
-- The wire of a generator is within the width

view-bound₁ : ∀ {n} (g : Gen n) {p h} → view g ≡ one p h → p < n
view-bound₁ (gate₀ ())
view-bound₁ (gate₁ h) Eq.refl = s≤s z≤n
view-bound₁ (gate₂ h) ()
view-bound₁ (g ↥) e with view g in eq
view-bound₁ (g ↥) Eq.refl | one p h = s≤s (view-bound₁ g eq)

view-bound₂ : ∀ {n} (g : Gen n) {p h} → view g ≡ two p h → suc p < n
view-bound₂ (gate₀ ())
view-bound₂ (gate₁ h) ()
view-bound₂ (gate₂ h) Eq.refl = s≤s (s≤s z≤n)
view-bound₂ (g ↥) e with view g in eq
view-bound₂ (g ↥) Eq.refl | two p h = s≤s (view-bound₂ g eq)

------------------------------------------------------------------------
-- One-wire gates

module _ {m : ℕ} where
  private
    n : ℕ
    n = ₃₊ m

  -- The context and the pairing bit of a basis vector, for a gate on
  -- wire p: the pairing wire is p − 1, or the top wire for p = 0.
  ctx₁ : ℕ → Bits n → Bits (₁₊ m)
  ctx₁ zero    x = removeℕ (₁₊ m) (removeℕ 0 x)
  ctx₁ (suc p) x = removeℕ p (removeℕ (suc p) x)

  pr₁ : ℕ → Bits n → Bool
  pr₁ zero    x = lookupℕ (₂₊ m) x
  pr₁ (suc p) x = lookupℕ p x

  -- Reading the context, the pairing bit and the gate bit off the
  -- vector they were written into.
  ctx-str₁ : ∀ p c b g → p < n → ctx₁ p (str₁ p c b g) ≡ c
  ctx-str₁ zero    c b g _       = remove-insert (₁₊ m) b c ≤-refl
  ctx-str₁ (suc p) c b g (s≤s q) =
    Eq.trans (Eq.cong (removeℕ p) (remove-insert (suc p) g (insertℕ p b c) q))
             (remove-insert p b c (≤-pred q))

  pr-str₁ : ∀ p c b g → p < n → pr₁ p (str₁ p c b g) ≡ b
  pr-str₁ zero    c b g _       = lookup-insert (₁₊ m) b c ≤-refl
  pr-str₁ (suc p) c b g (s≤s q) =
    Eq.trans (lookup-insert-below (suc p) p g (insertℕ p b c) ≤-refl q)
             (lookup-insert p b c (≤-pred q))

  bit-str₁ : ∀ p (c : Bits (₁₊ m)) b g → p < n → lookupℕ p (str₁ p c b g) ≡ g
  bit-str₁ zero    c b g _       = Eq.refl
  bit-str₁ (suc p) c b g (s≤s q) = lookup-insert (suc p) g (insertℕ p b c) q

  -- A basis vector is the vector written from its own context, pairing
  -- bit and gate bit.
  str-ctx₁ : ∀ p x → p < n → str₁ p (ctx₁ p x) (pr₁ p x) (lookupℕ p x) ≡ x
  str-ctx₁ zero    (x₀ ∷ x) _       =
    Eq.cong (x₀ ∷_) (insert-lookup-remove (₁₊ m) x ≤-refl)
  str-ctx₁ (suc p) x       (s≤s q) =
    Eq.trans
      (Eq.cong (λ v → insertℕ (suc p) (lookupℕ (suc p) x) (insertℕ p v (removeℕ p (removeℕ (suc p) x))))
        (Eq.sym (lookup-remove-below (suc p) p x ≤-refl q)))
      (Eq.trans
        (Eq.cong (insertℕ (suc p) (lookupℕ (suc p) x)) (insert-lookup-remove p (removeℕ (suc p) x) (≤-pred q)))
        (insert-lookup-remove (suc p) x q))

  -- Consequently a basis vector with gate bit g is the vector of its
  -- context and pairing bit, and vectors of different contexts differ.
  str₁-≡ : ∀ p x c b → p < n → ctx₁ p x ≡ c → pr₁ p x ≡ b → x ≡ str₁ p c b (lookupℕ p x)
  str₁-≡ p x c b q ec eb =
    Eq.trans (Eq.sym (str-ctx₁ p x q)) (Eq.cong₂ (λ c′ b′ → str₁ p c′ b′ (lookupℕ p x)) ec eb)

------------------------------------------------------------------------
-- Two-wire gates, on wires p and p + 1

  ctx₂ : ℕ → Bits n → Bits m
  ctx₂ zero    x = removeℕ m (removeℕ 0 (removeℕ 0 x))
  ctx₂ (suc p) x = removeℕ p (removeℕ (suc p) (removeℕ (₂₊ p) x))

  pr₂ : ℕ → Bits n → Bool
  pr₂ zero    x = lookupℕ (₂₊ m) x
  pr₂ (suc p) x = lookupℕ p x

  ctx-str₂ : ∀ p c b u t → suc p < n → ctx₂ p (str₂ p c b u t) ≡ c
  ctx-str₂ zero    c b u t _             = remove-insert m b c ≤-refl
  ctx-str₂ (suc p) c b u t (s≤s (s≤s q)) =
    Eq.trans (Eq.cong (λ v → removeℕ p (removeℕ (suc p) v))
               (remove-insert (₂₊ p) u (insertℕ (suc p) t (insertℕ p b c)) (s≤s q)))
      (Eq.trans (Eq.cong (removeℕ p) (remove-insert (suc p) t (insertℕ p b c) q))
        (remove-insert p b c (≤-pred q)))

  pr-str₂ : ∀ p c b u t → suc p < n → pr₂ p (str₂ p c b u t) ≡ b
  pr-str₂ zero    c b u t _             = lookup-insert m b c ≤-refl
  pr-str₂ (suc p) c b u t (s≤s (s≤s q)) =
    Eq.trans (lookup-insert-below (₂₊ p) p u (insertℕ (suc p) t (insertℕ p b c)) (n≤1+n _) (s≤s q))
      (Eq.trans (lookup-insert-below (suc p) p t (insertℕ p b c) ≤-refl q)
        (lookup-insert p b c (≤-pred q)))

  bit-str₂ : ∀ p (c : Bits m) b u t → suc p < n → lookupℕ p (str₂ p c b u t) ≡ t
  bit-str₂ zero    c b u t _             = Eq.refl
  bit-str₂ (suc p) c b u t (s≤s (s≤s q)) =
    Eq.trans (lookup-insert-below (₂₊ p) (suc p) u (insertℕ (suc p) t (insertℕ p b c)) ≤-refl (s≤s q))
      (lookup-insert (suc p) t (insertℕ p b c) q)

  ctl-str₂ : ∀ p (c : Bits m) b u t → suc p < n → lookupℕ (suc p) (str₂ p c b u t) ≡ u
  ctl-str₂ zero    c b u t _             = Eq.refl
  ctl-str₂ (suc p) c b u t (s≤s (s≤s q)) = lookup-insert (₂₊ p) u (insertℕ (suc p) t (insertℕ p b c)) (s≤s q)

  str-ctx₂ : ∀ p x → suc p < n →
             str₂ p (ctx₂ p x) (pr₂ p x) (lookupℕ (suc p) x) (lookupℕ p x) ≡ x
  str-ctx₂ zero    (x₀ ∷ x₁ ∷ x) _ =
    Eq.cong (λ v → x₀ ∷ x₁ ∷ v) (insert-lookup-remove m x ≤-refl)
  str-ctx₂ (suc p) x (s≤s (s≤s q)) =
    let x′  = removeℕ (₂₊ p) x
        x″  = removeℕ (suc p) x′
    in Eq.trans
      (Eq.cong₂ (λ v w → insertℕ (₂₊ p) (lookupℕ (₂₊ p) x) (insertℕ (suc p) v (insertℕ p w (removeℕ p x″))))
        (Eq.sym (lookup-remove-below (₂₊ p) (suc p) x ≤-refl (s≤s q)))
        (Eq.sym (Eq.trans (lookup-remove-below (suc p) p x′ ≤-refl q)
                          (lookup-remove-below (₂₊ p) p x (n≤1+n _) (s≤s q)))))
      (Eq.trans
        (Eq.cong (λ v → insertℕ (₂₊ p) (lookupℕ (₂₊ p) x) (insertℕ (suc p) (lookupℕ (suc p) x′) v))
          (insert-lookup-remove p x″ (≤-pred q)))
        (Eq.trans
          (Eq.cong (insertℕ (₂₊ p) (lookupℕ (₂₊ p) x)) (insert-lookup-remove (suc p) x′ q))
          (insert-lookup-remove (₂₊ p) x (s≤s q))))

  str₂-≡ : ∀ p x c b u → suc p < n → ctx₂ p x ≡ c → pr₂ p x ≡ b → lookupℕ (suc p) x ≡ u →
           x ≡ str₂ p c b u (lookupℕ p x)
  str₂-≡ p x c b u q ec eb eu =
    Eq.trans (Eq.sym (str-ctx₂ p x q))
      (Eq.trans (Eq.cong₂ (λ c′ b′ → str₂ p c′ b′ (lookupℕ (suc p) x) (lookupℕ p x)) ec eb)
        (Eq.cong (λ u′ → str₂ p c b u′ (lookupℕ p x)) eu))
