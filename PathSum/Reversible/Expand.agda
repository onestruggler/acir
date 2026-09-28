------------------------------------------------------------------------
-- Presentations of groups
--
-- Netlists of Toffoli and CNOT gates, expanded into Clifford+T (Amy,
-- QPL 2018, section 5.2)
--
-- Section 5.2's reversible circuits are netlists "which are then
-- expanded to the Clifford+T gate set".  PathSum.Toffoli.Netlist does
-- this for netlists of Toffoli gates alone; here it is for the
-- netlists of PathSum.Reversible, which have CNOTs too.  A Toffoli
-- gate becomes the seven-T circuit of PathSum.Toffoli, a CNOT stays a
-- CNOT (expand), and the circuit computes the netlist's Boolean
-- function (expand-computes): its operator is the permutation matrix
-- of run gs, up to its normalisation.  The proof is by induction on
-- the netlist, through PathSum.Classical's ⟦++⟧-computes (by
-- proposition 2.7, a composite of path-sums computing Boolean
-- functions computes the composite function), PathSum.Toffoli's
-- tof-computes and PathSum.Classical's ⟦CNOT⟧-computes; the netlist's
-- Boolean function is PathSum.Reversible's run, head first, like a
-- circuit.  No path-sum is computed.
--
-- Resources, for comparison with the paper's table 2: each Toffoli
-- gate contributes two Hadamards, hence two path variables
-- (norm-expand, paths-expand), and seven T or T† gates
-- (tcount-expand); the circuit has fifteen gates per Toffoli gate and
-- one per CNOT (length-expand), so eight Clifford gates per Toffoli
-- gate besides the CNOTs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Reversible.Expand (M₀ : ℕ) where

open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat.Base using (_+_; _*_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Classical M₀ using
  (_computes_; ⟦++⟧-computes; ⟦[]⟧-computes; ⟦CNOT⟧-computes)
open import PathSum.Compose.CRK M₀ using (norm-++)
open import PathSum.CRK.Circuit M using (paths≡norm)
open import PathSum.CRK.Path M₀ using (CNOT; Circuit; ⟦_⟧; norm; paths)
open import PathSum.Reversible using
  (Gate; ccx; cx; run; recover; toffolis; cnots)
open import PathSum.Toffoli M₀ using (tof; tof-computes)
open import PathSum.Toffoli.Netlist M₀ using (tcount; tcount-++)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The expansion

-- A Toffoli gate as the seven-T circuit, a CNOT as itself.

expand : List (Gate n) → Circuit n
expand []                       = []
expand (ccx c₁ c₂ t p q r ∷ gs) =
  tof c₁ c₂ t (recover p) (recover q) (recover r) ++ expand gs
expand (cx c t p ∷ gs)          = CNOT c t (recover p) ∷ expand gs

-- It computes the netlist's Boolean function.

expand-computes : (gs : List (Gate n)) → ⟦ expand gs ⟧ computes run gs
expand-computes []                       = ⟦[]⟧-computes
expand-computes (ccx c₁ c₂ t p q r ∷ gs) =
  ⟦++⟧-computes (tof c₁ c₂ t (recover p) (recover q) (recover r)) (expand gs)
                (tof-computes c₁ c₂ t (recover p) (recover q) (recover r))
                (expand-computes gs)
expand-computes (cx c t p ∷ gs)          =
  ⟦++⟧-computes (CNOT c t (recover p) ∷ []) (expand gs)
                (⟦CNOT⟧-computes c t (recover p)) (expand-computes gs)


------------------------------------------------------------------------
-- Resources

-- Two Hadamards, hence two path variables, and seven T or T† gates per
-- Toffoli gate.

norm-expand : (gs : List (Gate n)) → norm (expand gs) ≡ toffolis gs * 2
norm-expand []                       = refl
norm-expand (ccx c₁ c₂ t p q r ∷ gs) =
  trans (norm-++ (tof c₁ c₂ t (recover p) (recover q) (recover r))
                 (expand gs))
        (cong (2 +_) (norm-expand gs))
norm-expand (cx c t p ∷ gs)          = norm-expand gs

paths-expand : (gs : List (Gate n)) → paths (expand gs) ≡ toffolis gs * 2
paths-expand gs = trans (paths≡norm (expand gs)) (norm-expand gs)

tcount-expand : (gs : List (Gate n)) → tcount (expand gs) ≡ toffolis gs * 7
tcount-expand []                       = refl
tcount-expand (ccx c₁ c₂ t p q r ∷ gs) =
  trans (tcount-++ (tof c₁ c₂ t (recover p) (recover q) (recover r))
                   (expand gs))
        (cong (7 +_) (tcount-expand gs))
tcount-expand (cx c t p ∷ gs)          = tcount-expand gs

-- Fifteen gates per Toffoli gate, one per CNOT.

length-expand : (gs : List (Gate n)) →
                length (expand gs) ≡ toffolis gs * 15 + cnots gs
length-expand []                       = refl
length-expand (ccx c₁ c₂ t p q r ∷ gs) =
  trans (length-++ (tof c₁ c₂ t (recover p) (recover q) (recover r))
                   {expand gs})
        (cong (15 +_) (length-expand gs))
length-expand (cx c t p ∷ gs)          =
  trans (cong suc (length-expand gs))
        (sym (+-suc (toffolis gs * 15) (cnots gs)))
