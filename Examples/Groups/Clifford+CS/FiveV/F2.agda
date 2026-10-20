------------------------------------------------------------------------
-- Presentations of groups
--
-- (F2): controlled gates on disjoint wires commute
--
-- λ¹ g and λ¹ h commute on five wires for generators g, h of the
-- four-wire domain on disjoint wires (the paper's (F2)): the
-- derivations Five.D (scratchpad/joint/f2.py), from four-wire windows
-- and, for the two disjoint CS gates, the five-wire rule AX.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.F2 where

open import Relation.Binary.PropositionalEquality as Eq using ()
open import Data.Bool using (Bool ; true ; false ; T)
open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ ; λ¹)
open import Examples.Groups.Clifford+CS.FiveV.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Flat using (by-flat)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F2-CS0-CS2)

-- Two generators on disjoint wires (the scalar is disjoint from all).
apart : Gen 4 → Gen 4 → Bool
apart (I-gen) (I-gen) = true
apart (I-gen) (I-gen ↥) = true
apart (I-gen) (I-gen ↥ ↥) = true
apart (I-gen) (I-gen ↥ ↥ ↥) = true
apart (I-gen) (I-gen ↥ ↥ ↥ ↥) = true
apart (I-gen) (S-gen) = true
apart (I-gen) (S-gen ↥) = true
apart (I-gen) (S-gen ↥ ↥) = true
apart (I-gen) (S-gen ↥ ↥ ↥) = true
apart (I-gen) (K-gen) = true
apart (I-gen) (K-gen ↥) = true
apart (I-gen) (K-gen ↥ ↥) = true
apart (I-gen) (K-gen ↥ ↥ ↥) = true
apart (I-gen) (CS-gen) = true
apart (I-gen) (CS-gen ↥) = true
apart (I-gen) (CS-gen ↥ ↥) = true
apart (I-gen ↥) (I-gen) = true
apart (I-gen ↥) (I-gen ↥) = true
apart (I-gen ↥) (I-gen ↥ ↥) = true
apart (I-gen ↥) (I-gen ↥ ↥ ↥) = true
apart (I-gen ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (I-gen ↥) (S-gen) = true
apart (I-gen ↥) (S-gen ↥) = true
apart (I-gen ↥) (S-gen ↥ ↥) = true
apart (I-gen ↥) (S-gen ↥ ↥ ↥) = true
apart (I-gen ↥) (K-gen) = true
apart (I-gen ↥) (K-gen ↥) = true
apart (I-gen ↥) (K-gen ↥ ↥) = true
apart (I-gen ↥) (K-gen ↥ ↥ ↥) = true
apart (I-gen ↥) (CS-gen) = true
apart (I-gen ↥) (CS-gen ↥) = true
apart (I-gen ↥) (CS-gen ↥ ↥) = true
apart (I-gen ↥ ↥) (I-gen) = true
apart (I-gen ↥ ↥) (I-gen ↥) = true
apart (I-gen ↥ ↥) (I-gen ↥ ↥) = true
apart (I-gen ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (I-gen ↥ ↥) (S-gen) = true
apart (I-gen ↥ ↥) (S-gen ↥) = true
apart (I-gen ↥ ↥) (S-gen ↥ ↥) = true
apart (I-gen ↥ ↥) (S-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥) (K-gen) = true
apart (I-gen ↥ ↥) (K-gen ↥) = true
apart (I-gen ↥ ↥) (K-gen ↥ ↥) = true
apart (I-gen ↥ ↥) (K-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥) (CS-gen) = true
apart (I-gen ↥ ↥) (CS-gen ↥) = true
apart (I-gen ↥ ↥) (CS-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (I-gen) = true
apart (I-gen ↥ ↥ ↥) (I-gen ↥) = true
apart (I-gen ↥ ↥ ↥) (I-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (S-gen) = true
apart (I-gen ↥ ↥ ↥) (S-gen ↥) = true
apart (I-gen ↥ ↥ ↥) (S-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (S-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (K-gen) = true
apart (I-gen ↥ ↥ ↥) (K-gen ↥) = true
apart (I-gen ↥ ↥ ↥) (K-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (K-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥) (CS-gen) = true
apart (I-gen ↥ ↥ ↥) (CS-gen ↥) = true
apart (I-gen ↥ ↥ ↥) (CS-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (I-gen) = true
apart (I-gen ↥ ↥ ↥ ↥) (I-gen ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (I-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (S-gen) = true
apart (I-gen ↥ ↥ ↥ ↥) (S-gen ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (S-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (S-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (K-gen) = true
apart (I-gen ↥ ↥ ↥ ↥) (K-gen ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (K-gen ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (K-gen ↥ ↥ ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (CS-gen) = true
apart (I-gen ↥ ↥ ↥ ↥) (CS-gen ↥) = true
apart (I-gen ↥ ↥ ↥ ↥) (CS-gen ↥ ↥) = true
apart (S-gen) (I-gen) = true
apart (S-gen) (I-gen ↥) = true
apart (S-gen) (I-gen ↥ ↥) = true
apart (S-gen) (I-gen ↥ ↥ ↥) = true
apart (S-gen) (I-gen ↥ ↥ ↥ ↥) = true
apart (S-gen) (S-gen) = false
apart (S-gen) (S-gen ↥) = true
apart (S-gen) (S-gen ↥ ↥) = true
apart (S-gen) (S-gen ↥ ↥ ↥) = true
apart (S-gen) (K-gen) = false
apart (S-gen) (K-gen ↥) = true
apart (S-gen) (K-gen ↥ ↥) = true
apart (S-gen) (K-gen ↥ ↥ ↥) = true
apart (S-gen) (CS-gen) = false
apart (S-gen) (CS-gen ↥) = true
apart (S-gen) (CS-gen ↥ ↥) = true
apart (S-gen ↥) (I-gen) = true
apart (S-gen ↥) (I-gen ↥) = true
apart (S-gen ↥) (I-gen ↥ ↥) = true
apart (S-gen ↥) (I-gen ↥ ↥ ↥) = true
apart (S-gen ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (S-gen ↥) (S-gen) = true
apart (S-gen ↥) (S-gen ↥) = false
apart (S-gen ↥) (S-gen ↥ ↥) = true
apart (S-gen ↥) (S-gen ↥ ↥ ↥) = true
apart (S-gen ↥) (K-gen) = true
apart (S-gen ↥) (K-gen ↥) = false
apart (S-gen ↥) (K-gen ↥ ↥) = true
apart (S-gen ↥) (K-gen ↥ ↥ ↥) = true
apart (S-gen ↥) (CS-gen) = false
apart (S-gen ↥) (CS-gen ↥) = false
apart (S-gen ↥) (CS-gen ↥ ↥) = true
apart (S-gen ↥ ↥) (I-gen) = true
apart (S-gen ↥ ↥) (I-gen ↥) = true
apart (S-gen ↥ ↥) (I-gen ↥ ↥) = true
apart (S-gen ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (S-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (S-gen ↥ ↥) (S-gen) = true
apart (S-gen ↥ ↥) (S-gen ↥) = true
apart (S-gen ↥ ↥) (S-gen ↥ ↥) = false
apart (S-gen ↥ ↥) (S-gen ↥ ↥ ↥) = true
apart (S-gen ↥ ↥) (K-gen) = true
apart (S-gen ↥ ↥) (K-gen ↥) = true
apart (S-gen ↥ ↥) (K-gen ↥ ↥) = false
apart (S-gen ↥ ↥) (K-gen ↥ ↥ ↥) = true
apart (S-gen ↥ ↥) (CS-gen) = true
apart (S-gen ↥ ↥) (CS-gen ↥) = false
apart (S-gen ↥ ↥) (CS-gen ↥ ↥) = false
apart (S-gen ↥ ↥ ↥) (I-gen) = true
apart (S-gen ↥ ↥ ↥) (I-gen ↥) = true
apart (S-gen ↥ ↥ ↥) (I-gen ↥ ↥) = true
apart (S-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (S-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (S-gen ↥ ↥ ↥) (S-gen) = true
apart (S-gen ↥ ↥ ↥) (S-gen ↥) = true
apart (S-gen ↥ ↥ ↥) (S-gen ↥ ↥) = true
apart (S-gen ↥ ↥ ↥) (S-gen ↥ ↥ ↥) = false
apart (S-gen ↥ ↥ ↥) (K-gen) = true
apart (S-gen ↥ ↥ ↥) (K-gen ↥) = true
apart (S-gen ↥ ↥ ↥) (K-gen ↥ ↥) = true
apart (S-gen ↥ ↥ ↥) (K-gen ↥ ↥ ↥) = false
apart (S-gen ↥ ↥ ↥) (CS-gen) = true
apart (S-gen ↥ ↥ ↥) (CS-gen ↥) = true
apart (S-gen ↥ ↥ ↥) (CS-gen ↥ ↥) = false
apart (K-gen) (I-gen) = true
apart (K-gen) (I-gen ↥) = true
apart (K-gen) (I-gen ↥ ↥) = true
apart (K-gen) (I-gen ↥ ↥ ↥) = true
apart (K-gen) (I-gen ↥ ↥ ↥ ↥) = true
apart (K-gen) (S-gen) = false
apart (K-gen) (S-gen ↥) = true
apart (K-gen) (S-gen ↥ ↥) = true
apart (K-gen) (S-gen ↥ ↥ ↥) = true
apart (K-gen) (K-gen) = false
apart (K-gen) (K-gen ↥) = true
apart (K-gen) (K-gen ↥ ↥) = true
apart (K-gen) (K-gen ↥ ↥ ↥) = true
apart (K-gen) (CS-gen) = false
apart (K-gen) (CS-gen ↥) = true
apart (K-gen) (CS-gen ↥ ↥) = true
apart (K-gen ↥) (I-gen) = true
apart (K-gen ↥) (I-gen ↥) = true
apart (K-gen ↥) (I-gen ↥ ↥) = true
apart (K-gen ↥) (I-gen ↥ ↥ ↥) = true
apart (K-gen ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (K-gen ↥) (S-gen) = true
apart (K-gen ↥) (S-gen ↥) = false
apart (K-gen ↥) (S-gen ↥ ↥) = true
apart (K-gen ↥) (S-gen ↥ ↥ ↥) = true
apart (K-gen ↥) (K-gen) = true
apart (K-gen ↥) (K-gen ↥) = false
apart (K-gen ↥) (K-gen ↥ ↥) = true
apart (K-gen ↥) (K-gen ↥ ↥ ↥) = true
apart (K-gen ↥) (CS-gen) = false
apart (K-gen ↥) (CS-gen ↥) = false
apart (K-gen ↥) (CS-gen ↥ ↥) = true
apart (K-gen ↥ ↥) (I-gen) = true
apart (K-gen ↥ ↥) (I-gen ↥) = true
apart (K-gen ↥ ↥) (I-gen ↥ ↥) = true
apart (K-gen ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (K-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (K-gen ↥ ↥) (S-gen) = true
apart (K-gen ↥ ↥) (S-gen ↥) = true
apart (K-gen ↥ ↥) (S-gen ↥ ↥) = false
apart (K-gen ↥ ↥) (S-gen ↥ ↥ ↥) = true
apart (K-gen ↥ ↥) (K-gen) = true
apart (K-gen ↥ ↥) (K-gen ↥) = true
apart (K-gen ↥ ↥) (K-gen ↥ ↥) = false
apart (K-gen ↥ ↥) (K-gen ↥ ↥ ↥) = true
apart (K-gen ↥ ↥) (CS-gen) = true
apart (K-gen ↥ ↥) (CS-gen ↥) = false
apart (K-gen ↥ ↥) (CS-gen ↥ ↥) = false
apart (K-gen ↥ ↥ ↥) (I-gen) = true
apart (K-gen ↥ ↥ ↥) (I-gen ↥) = true
apart (K-gen ↥ ↥ ↥) (I-gen ↥ ↥) = true
apart (K-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (K-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (K-gen ↥ ↥ ↥) (S-gen) = true
apart (K-gen ↥ ↥ ↥) (S-gen ↥) = true
apart (K-gen ↥ ↥ ↥) (S-gen ↥ ↥) = true
apart (K-gen ↥ ↥ ↥) (S-gen ↥ ↥ ↥) = false
apart (K-gen ↥ ↥ ↥) (K-gen) = true
apart (K-gen ↥ ↥ ↥) (K-gen ↥) = true
apart (K-gen ↥ ↥ ↥) (K-gen ↥ ↥) = true
apart (K-gen ↥ ↥ ↥) (K-gen ↥ ↥ ↥) = false
apart (K-gen ↥ ↥ ↥) (CS-gen) = true
apart (K-gen ↥ ↥ ↥) (CS-gen ↥) = true
apart (K-gen ↥ ↥ ↥) (CS-gen ↥ ↥) = false
apart (CS-gen) (I-gen) = true
apart (CS-gen) (I-gen ↥) = true
apart (CS-gen) (I-gen ↥ ↥) = true
apart (CS-gen) (I-gen ↥ ↥ ↥) = true
apart (CS-gen) (I-gen ↥ ↥ ↥ ↥) = true
apart (CS-gen) (S-gen) = false
apart (CS-gen) (S-gen ↥) = false
apart (CS-gen) (S-gen ↥ ↥) = true
apart (CS-gen) (S-gen ↥ ↥ ↥) = true
apart (CS-gen) (K-gen) = false
apart (CS-gen) (K-gen ↥) = false
apart (CS-gen) (K-gen ↥ ↥) = true
apart (CS-gen) (K-gen ↥ ↥ ↥) = true
apart (CS-gen) (CS-gen) = false
apart (CS-gen) (CS-gen ↥) = false
apart (CS-gen) (CS-gen ↥ ↥) = true
apart (CS-gen ↥) (I-gen) = true
apart (CS-gen ↥) (I-gen ↥) = true
apart (CS-gen ↥) (I-gen ↥ ↥) = true
apart (CS-gen ↥) (I-gen ↥ ↥ ↥) = true
apart (CS-gen ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (CS-gen ↥) (S-gen) = true
apart (CS-gen ↥) (S-gen ↥) = false
apart (CS-gen ↥) (S-gen ↥ ↥) = false
apart (CS-gen ↥) (S-gen ↥ ↥ ↥) = true
apart (CS-gen ↥) (K-gen) = true
apart (CS-gen ↥) (K-gen ↥) = false
apart (CS-gen ↥) (K-gen ↥ ↥) = false
apart (CS-gen ↥) (K-gen ↥ ↥ ↥) = true
apart (CS-gen ↥) (CS-gen) = false
apart (CS-gen ↥) (CS-gen ↥) = false
apart (CS-gen ↥) (CS-gen ↥ ↥) = false
apart (CS-gen ↥ ↥) (I-gen) = true
apart (CS-gen ↥ ↥) (I-gen ↥) = true
apart (CS-gen ↥ ↥) (I-gen ↥ ↥) = true
apart (CS-gen ↥ ↥) (I-gen ↥ ↥ ↥) = true
apart (CS-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) = true
apart (CS-gen ↥ ↥) (S-gen) = true
apart (CS-gen ↥ ↥) (S-gen ↥) = true
apart (CS-gen ↥ ↥) (S-gen ↥ ↥) = false
apart (CS-gen ↥ ↥) (S-gen ↥ ↥ ↥) = false
apart (CS-gen ↥ ↥) (K-gen) = true
apart (CS-gen ↥ ↥) (K-gen ↥) = true
apart (CS-gen ↥ ↥) (K-gen ↥ ↥) = false
apart (CS-gen ↥ ↥) (K-gen ↥ ↥ ↥) = false
apart (CS-gen ↥ ↥) (CS-gen) = true
apart (CS-gen ↥ ↥) (CS-gen ↥) = false
apart (CS-gen ↥ ↥) (CS-gen ↥ ↥) = false

f2 : Ws → (g h : Gen 4) → T (apart g h) → 5 ⊢ₓ λ¹ g • λ¹ h ≈ λ¹ h • λ¹ g
f2 c4 (I-gen) (I-gen) _ = refl
f2 c4 (I-gen) (I-gen ↥) _ = refl
f2 c4 (I-gen) (I-gen ↥ ↥) _ = refl
f2 c4 (I-gen) (I-gen ↥ ↥ ↥) _ = refl
f2 c4 (I-gen) (I-gen ↥ ↥ ↥ ↥) _ = refl
f2 c4 (I-gen) (S-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (S-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (S-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl))
f2 c4 (I-gen) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (I-gen) _ = refl
f2 c4 (I-gen ↥) (I-gen ↥) _ = refl
f2 c4 (I-gen ↥) (I-gen ↥ ↥) _ = refl
f2 c4 (I-gen ↥) (I-gen ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥) (I-gen ↥ ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥) (S-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (S-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (S-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (I-gen) _ = refl
f2 c4 (I-gen ↥ ↥) (I-gen ↥) _ = refl
f2 c4 (I-gen ↥ ↥) (I-gen ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥) (I-gen ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥) (S-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (S-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (S-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (I-gen) _ = refl
f2 c4 (I-gen ↥ ↥ ↥) (I-gen ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥) (I-gen ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥) (S-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (S-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (S-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (I-gen) _ = refl
f2 c4 (I-gen ↥ ↥ ↥ ↥) (I-gen ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥ ↥) (I-gen ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥ ↥) (I-gen ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = refl
f2 c4 (I-gen ↥ ↥ ↥ ↥) (S-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (S-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (S-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl))
f2 c4 (I-gen ↥ ↥ ↥ ↥) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl)))
f2 c4 (S-gen) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl)))
f2 c4 (S-gen) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl)))
f2 c4 (S-gen) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl)))
f2 c4 (S-gen) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S0 c4) (by-flat Eq.refl)))
f2 c4 (S-gen) (S-gen) ()
f2 c4 (S-gen) (S-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-S1 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (S-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-S2 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-S3 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (K-gen) ()
f2 c4 (S-gen) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-K1 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-K2 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-K3 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (CS-gen) ()
f2 c4 (S-gen) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-CS1 c4) (by-flat Eq.refl))
f2 c4 (S-gen) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S0-CS2 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S1 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-S1 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥) (S-gen ↥) ()
f2 c4 (S-gen ↥) (S-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S1-S2 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S1-S3 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-S1-K0 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥) (K-gen ↥) ()
f2 c4 (S-gen ↥) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S1-K2 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S1-K3 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥) (CS-gen) ()
f2 c4 (S-gen ↥) (CS-gen ↥) ()
f2 c4 (S-gen ↥) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S1-CS2 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S2 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-S2 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥) (S-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S1-S2 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥) (S-gen ↥ ↥) ()
f2 c4 (S-gen ↥ ↥) (S-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S2-S3 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-S2-K0 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S2-K1 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥) (K-gen ↥ ↥) ()
f2 c4 (S-gen ↥ ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S2-K3 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-S2-CS0 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥) (CS-gen ↥) ()
f2 c4 (S-gen ↥ ↥) (CS-gen ↥ ↥) ()
f2 c4 (S-gen ↥ ↥ ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (S-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S1-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (S-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S2-S3 c4) (by-flat Eq.refl)))
f2 c4 (S-gen ↥ ↥ ↥) (S-gen ↥ ↥ ↥) ()
f2 c4 (S-gen ↥ ↥ ↥) (K-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-S3-K0 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥ ↥) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S3-K1 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥ ↥) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S3-K2 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥ ↥) (K-gen ↥ ↥ ↥) ()
f2 c4 (S-gen ↥ ↥ ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-S3-CS0 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥ ↥) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-S3-CS1 c4) (by-flat Eq.refl))
f2 c4 (S-gen ↥ ↥ ↥) (CS-gen ↥ ↥) ()
f2 c4 (K-gen) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (S-gen) ()
f2 c4 (K-gen) (S-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S1-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (S-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S2-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (S-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S3-K0 c4) (by-flat Eq.refl)))
f2 c4 (K-gen) (K-gen) ()
f2 c4 (K-gen) (K-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K0-K1 c4) (by-flat Eq.refl))
f2 c4 (K-gen) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K0-K2 c4) (by-flat Eq.refl))
f2 c4 (K-gen) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K0-K3 c4) (by-flat Eq.refl))
f2 c4 (K-gen) (CS-gen) ()
f2 c4 (K-gen) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K0-CS1 c4) (by-flat Eq.refl))
f2 c4 (K-gen) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K0-CS2 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (S-gen ↥) ()
f2 c4 (K-gen ↥) (S-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S2-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (S-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S3-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (K-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K0-K1 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥) (K-gen ↥) ()
f2 c4 (K-gen ↥) (K-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K1-K2 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K1-K3 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥) (CS-gen) ()
f2 c4 (K-gen ↥) (CS-gen ↥) ()
f2 c4 (K-gen ↥) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K1-CS2 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥ ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (S-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S1-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (S-gen ↥ ↥) ()
f2 c4 (K-gen ↥ ↥) (S-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S3-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (K-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K0-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (K-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K1-K2 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥) (K-gen ↥ ↥) ()
f2 c4 (K-gen ↥ ↥) (K-gen ↥ ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K2-K3 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥ ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-K2-CS0 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥ ↥) (CS-gen ↥) ()
f2 c4 (K-gen ↥ ↥) (CS-gen ↥ ↥) ()
f2 c4 (K-gen ↥ ↥ ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (S-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S1-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (S-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S2-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (S-gen ↥ ↥ ↥) ()
f2 c4 (K-gen ↥ ↥ ↥) (K-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K0-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (K-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K1-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (K-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K2-K3 c4) (by-flat Eq.refl)))
f2 c4 (K-gen ↥ ↥ ↥) (K-gen ↥ ↥ ↥) ()
f2 c4 (K-gen ↥ ↥ ↥) (CS-gen) _ = trans (by-flat Eq.refl) (trans (lem-F2-K3-CS0 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥ ↥ ↥) (CS-gen ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-K3-CS1 c4) (by-flat Eq.refl))
f2 c4 (K-gen ↥ ↥ ↥) (CS-gen ↥ ↥) ()
f2 c4 (CS-gen) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (S-gen) ()
f2 c4 (CS-gen) (S-gen ↥) ()
f2 c4 (CS-gen) (S-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S2-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (S-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S3-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (K-gen) ()
f2 c4 (CS-gen) (K-gen ↥) ()
f2 c4 (CS-gen) (K-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K2-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (K-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K3-CS0 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen) (CS-gen) ()
f2 c4 (CS-gen) (CS-gen ↥) ()
f2 c4 (CS-gen) (CS-gen ↥ ↥) _ = trans (by-flat Eq.refl) (trans (lem-F2-CS0-CS2 c4) (by-flat Eq.refl))
f2 c4 (CS-gen ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (S-gen ↥) ()
f2 c4 (CS-gen ↥) (S-gen ↥ ↥) ()
f2 c4 (CS-gen ↥) (S-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S3-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (K-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K0-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (K-gen ↥) ()
f2 c4 (CS-gen ↥) (K-gen ↥ ↥) ()
f2 c4 (CS-gen ↥) (K-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K3-CS1 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥) (CS-gen) ()
f2 c4 (CS-gen ↥) (CS-gen ↥) ()
f2 c4 (CS-gen ↥) (CS-gen ↥ ↥) ()
f2 c4 (CS-gen ↥ ↥) (I-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (I-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (I-gen ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (I-gen ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (I-gen ↥ ↥ ↥ ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-I-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (S-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S0-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (S-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-S1-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (S-gen ↥ ↥) ()
f2 c4 (CS-gen ↥ ↥) (S-gen ↥ ↥ ↥) ()
f2 c4 (CS-gen ↥ ↥) (K-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K0-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (K-gen ↥) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-K1-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (K-gen ↥ ↥) ()
f2 c4 (CS-gen ↥ ↥) (K-gen ↥ ↥ ↥) ()
f2 c4 (CS-gen ↥ ↥) (CS-gen) _ = sym (trans (by-flat Eq.refl) (trans (lem-F2-CS0-CS2 c4) (by-flat Eq.refl)))
f2 c4 (CS-gen ↥ ↥) (CS-gen ↥) ()
f2 c4 (CS-gen ↥ ↥) (CS-gen ↥ ↥) ()
