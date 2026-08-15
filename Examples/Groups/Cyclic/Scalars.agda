------------------------------------------------------------------------
-- Presentations of groups
--
-- The cyclic group of order N as a transport target.
--
-- ℤ/Nℤ counted in Fin N, and ℤ/Nℤ presented as words over one generator,
-- are the same group; this module gives the map one way,
--
--     emb k = T ^ toℕ k,
--
-- with the two facts a homomorphism needs: it is normalised (which is
-- definitional, T ^ 0 being ε) and multiplicative.  Multiplicativity is
-- the whole content, and it is modular arithmetic: Fin addition is ℕ
-- addition reduced mod N, and reducing the exponent is free because
-- T ^ N ≈ ε.
--
-- The order is written ₂₊ m so that it matches +-0-abelianGroup m, whose
-- carrier is ℤ (₂₊ m); an off-by-one there would silently change the
-- group.  Both scalar layers that use this — ℤ/8 for qubits, ℤ/pℤ for
-- qupits — are instances.
--
-- Only Normalization's `g` does anything like this already, and it is
-- not the same map: it goes to the normal forms of THIS presentation,
-- whereas emb's source is the Fin-valued group a semantic defect is
-- measured in.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

open import Notations

module Examples.Groups.Cyclic.Scalars (m : ℕ) where

open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat as Nat using (_%_ ; _/_)
open import Data.Nat.DivMod using (m%n<n ; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (*-comm)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; WRel ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP

open import ForStdlib.Data.Fin.Mod using (ℤ ; +-0-abelianGroup)
open import Algebra.Bundles using (AbelianGroup)

open import Examples.Groups.Cyclic.Syntactics using (X ; T ; _Cn,_===_ ; order)

------------------------------------------------------------------------
-- The order, the relation, and the group being transported from

N : ℕ
N = ₂₊ m

Γ : WRel X
Γ = N Cn,_===_

-- The Fin side: ℤ/Nℤ written additively.
A : AbelianGroup _ _
A = +-0-abelianGroup m

module A = AbelianGroup A
module B = PB Γ
module P = PP Γ

------------------------------------------------------------------------
-- The generator has order N
--
-- The axiom is stated over _^'_ (left-associated) and everything else
-- uses _^_, so the two are matched once, here.

T^N : B._≈_ (T ^ N) ε
T^N = B.trans (B.sym (P.^'=^ {N} {T})) (B.axiom order)

------------------------------------------------------------------------
-- Reducing an exponent modulo N
--
-- Split k as k % N + (k / N) * N and collapse the second summand with
-- T ^ N ≈ ε.

T^-% : ∀ k → B._≈_ (T ^ k) (T ^ (k % N))
T^-% k = begin
  T ^ k
    ≡⟨ Eq.cong (T ^_) (m≡m%n+[m/n]*n k N) ⟩
  T ^ (k % N Nat.+ (k / N) Nat.* N)
    ≈⟨ ^-+ T (k % N) ((k / N) Nat.* N) ⟩
  T ^ (k % N) • T ^ ((k / N) Nat.* N)
    ≈⟨ (cright refl' (Eq.cong (T ^_) (*-comm (k / N) N))) ⟩
  T ^ (k % N) • T ^ (N Nat.* (k / N))
    ≈⟨ (cright sym (^^ T N (k / N))) ⟩
  T ^ (k % N) • (T ^ N) ^ (k / N)
    ≈⟨ (cright ^-cong (T ^ N) ε (k / N) T^N) ⟩
  T ^ (k % N) • ε ^ (k / N)
    ≈⟨ (cright ε^k=ε (k / N)) ⟩
  T ^ (k % N) • ε
    ≈⟨ right-unit ⟩
  T ^ (k % N) ∎
  where
  open PB Γ
  open PP Γ
  open SR word-setoid

------------------------------------------------------------------------
-- The transport

emb : ℤ N → Word X
emb k = T ^ toℕ k

emb-cong : ∀ {j k} → j ≡ k → B._≈_ (emb j) (emb k)
emb-cong e = B.refl' (Eq.cong emb e)

emb-ε : B._≈_ (emb A.ε) ε
emb-ε = B.refl

private
  -- Fin addition is ℕ addition modulo N, on the nose.
  toℕ-∙ : (j k : ℤ N) → toℕ (j A.∙ k) ≡ (toℕ j Nat.+ toℕ k) % N
  toℕ-∙ j k = toℕ-fromℕ< (m%n<n (toℕ j Nat.+ toℕ k) N)

emb-∙ : (j k : ℤ N) → B._≈_ (emb (j A.∙ k)) (emb j • emb k)
emb-∙ j k = begin
  T ^ toℕ (j A.∙ k)              ≡⟨ Eq.cong (T ^_) (toℕ-∙ j k) ⟩
  T ^ ((toℕ j Nat.+ toℕ k) % N)  ≈⟨ sym (T^-% (toℕ j Nat.+ toℕ k)) ⟩
  T ^ (toℕ j Nat.+ toℕ k)        ≈⟨ ^-+ T (toℕ j) (toℕ k) ⟩
  T ^ toℕ j • T ^ toℕ k          ∎
  where
  open PB Γ
  open PP Γ
  open SR word-setoid
