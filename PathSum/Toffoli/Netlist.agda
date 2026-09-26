------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits of Toffoli gates, expanded into Clifford+T (Amy, QPL 2018,
-- section 5.2)
--
-- Section 5.2's reversible circuits -- n-bit Toffoli gates, adders --
-- are designed as circuits of Toffoli gates, "which are then expanded
-- to the Clifford+T gate set".  Here is that two-level view.  A Toffoli
-- gate is a record of three distinct wires (Toff: controls c₁, c₂ and
-- target t); a list of them is expanded gate by gate into the seven-T
-- circuit of PathSum.Toffoli (expand), and read classically as the
-- composite of the Toffoli functions (apply), the head of the list
-- first, like a circuit.  The theorem is that the expansion computes
-- that composite (expand-computes, by PathSum.Classical.⟦++⟧-computes
-- and PathSum.Toffoli.tof-computes, induction on the list): its
-- operator is the permutation matrix of apply gs, up to its
-- normalisation.  So the Clifford+T circuit is verified once and for
-- all through its Toffoli netlist, and what remains about a particular
-- netlist is a statement about Boolean functions.
--
-- Also here, for comparison with the resource counts of the paper's
-- table 2: each Toffoli gate contributes two Hadamards, hence two path
-- variables (norm-expand, paths-expand), seven T or T† gates
-- (tcount-expand), and fifteen gates in all (length-expand).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Toffoli.Netlist (M₀ : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat.Base using (_+_; _*_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Classical M₀ using
  (_computes_; ⟦++⟧-computes; ⟦[]⟧-computes)
open import PathSum.Compose.CRK M₀ using (norm-++)
open import PathSum.CRK.Circuit M using (paths≡norm)
open import PathSum.CRK.Path M₀ using
  (Gate; H; CNOT; R; R†; Circuit; ⟦_⟧; norm; paths)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Toffoli M₀ using (tof; toffoli; tof-computes)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Toffoli netlists

-- A Toffoli gate: controls c₁ and c₂, target t, all distinct.

record Toff (n : ℕ) : Set where
  constructor toff
  field
    c₁ c₂ t : Fin n
    c₁≢c₂  : c₁ ≢ c₂
    c₁≢t   : c₁ ≢ t
    c₂≢t   : c₂ ≢ t

-- Its expansion into Clifford+T: the seven-T circuit of
-- PathSum.Toffoli, gate by gate.

expand : List (Toff n) → Circuit n
expand []                          = []
expand (toff c₁ c₂ t p₁₂ p₁ p₂ ∷ gs) = tof c₁ c₂ t p₁₂ p₁ p₂ ++ expand gs

-- Its classical reading: the Toffoli functions composed, the head of
-- the list applied first.

apply : List (Toff n) → Assign n → Assign n
apply []                        x = x
apply (toff c₁ c₂ t _ _ _ ∷ gs) x = apply gs (toffoli c₁ c₂ t x)

apply-++ : (gs hs : List (Toff n)) (x : Assign n) →
           apply (gs ++ hs) x ≡ apply hs (apply gs x)
apply-++ []                        hs x = refl
apply-++ (toff c₁ c₂ t _ _ _ ∷ gs) hs x = apply-++ gs hs (toffoli c₁ c₂ t x)


------------------------------------------------------------------------
-- The expansion computes the netlist's function

expand-computes : (gs : List (Toff n)) → ⟦ expand gs ⟧ computes apply gs
expand-computes []                            = ⟦[]⟧-computes
expand-computes (toff c₁ c₂ t p₁₂ p₁ p₂ ∷ gs) =
  ⟦++⟧-computes (tof c₁ c₂ t p₁₂ p₁ p₂) (expand gs)
                (tof-computes c₁ c₂ t p₁₂ p₁ p₂) (expand-computes gs)


------------------------------------------------------------------------
-- Resource counts

-- The T and T† gates of a circuit (R 3 and R† 3).

tcount : Circuit n → ℕ
tcount []                           = 0
tcount (H _ ∷ C)                    = tcount C
tcount (CNOT _ _ _ ∷ C)             = tcount C
tcount (R (suc (suc (suc zero))) _ ∷ C)  = suc (tcount C)
tcount (R _ _ ∷ C)                  = tcount C
tcount (R† (suc (suc (suc zero))) _ ∷ C) = suc (tcount C)
tcount (R† _ _ ∷ C)                 = tcount C

tcount-++ : (C D : Circuit n) → tcount (C ++ D) ≡ tcount C + tcount D
tcount-++ []                                  D = refl
tcount-++ (H _ ∷ C)                           D = tcount-++ C D
tcount-++ (CNOT _ _ _ ∷ C)                    D = tcount-++ C D
tcount-++ (R (suc (suc (suc zero))) _ ∷ C)    D = cong suc (tcount-++ C D)
tcount-++ (R zero _ ∷ C)                      D = tcount-++ C D
tcount-++ (R (suc zero) _ ∷ C)                D = tcount-++ C D
tcount-++ (R (suc (suc zero)) _ ∷ C)          D = tcount-++ C D
tcount-++ (R (suc (suc (suc (suc _)))) _ ∷ C) D = tcount-++ C D
tcount-++ (R† (suc (suc (suc zero))) _ ∷ C)   D = cong suc (tcount-++ C D)
tcount-++ (R† zero _ ∷ C)                     D = tcount-++ C D
tcount-++ (R† (suc zero) _ ∷ C)               D = tcount-++ C D
tcount-++ (R† (suc (suc zero)) _ ∷ C)         D = tcount-++ C D
tcount-++ (R† (suc (suc (suc (suc _)))) _ ∷ C) D = tcount-++ C D

-- Per Toffoli gate: two Hadamards (so two path variables), seven T or
-- T† gates, fifteen gates.

norm-expand : (gs : List (Toff n)) → norm (expand gs) ≡ length gs * 2
norm-expand []                            = refl
norm-expand (toff c₁ c₂ t p₁₂ p₁ p₂ ∷ gs) =
  trans (norm-++ (tof c₁ c₂ t p₁₂ p₁ p₂) (expand gs))
        (cong (2 +_) (norm-expand gs))

paths-expand : (gs : List (Toff n)) → paths (expand gs) ≡ length gs * 2
paths-expand gs = trans (paths≡norm (expand gs)) (norm-expand gs)

tcount-expand : (gs : List (Toff n)) → tcount (expand gs) ≡ length gs * 7
tcount-expand []                            = refl
tcount-expand (toff c₁ c₂ t p₁₂ p₁ p₂ ∷ gs) =
  trans (tcount-++ (tof c₁ c₂ t p₁₂ p₁ p₂) (expand gs))
        (cong (7 +_) (tcount-expand gs))

length-expand : (gs : List (Toff n)) → length (expand gs) ≡ length gs * 15
length-expand []                            = refl
length-expand (toff c₁ c₂ t p₁₂ p₁ p₂ ∷ gs) =
  trans (length-++ (tof c₁ c₂ t p₁₂ p₁ p₂) {expand gs})
        (cong (15 +_) (length-expand gs))
