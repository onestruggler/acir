------------------------------------------------------------------------
-- Presentations of groups
--
-- From CCX+HH to CCX+H: completeness on four or more wires.
--
-- Two CCX+H circuits on 4 + n wires with the same matrix are, by
-- Elim, θ a • H^p and θ b • H^q.  θ of a CCX+HH circuit has an even
-- number of H, H^p has p, and the parity of the number of H is a
-- matrix invariant (GeneralN.HadamardParity), so p = q; cancelling H^p,
-- θ a and θ b have the same matrix, which is that of the expansion of
-- the CCX+HH circuits τ a and τ b (Soundness.τH-θ), so τ a and τ b have
-- the same matrix (the expansion reflects it, GeneralN.
-- HadamardEmbedding.reflect).  Completeness of CCX+HH.NaturalP with the
-- schema at the width gives a ≈ b, and θ carries the derivation over
-- (Transfer).  So the CCX+H rules are complete at every width from
-- four on if CCX+HH's are complete on at most twelve wires
-- (`from-twelve`), and at every width if moreover they are complete on
-- at most three (`every-width`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Complete where

open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Nat.Base using (ℕ ; _≤_ ; _∸_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₄₊)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Presentation.Base as PB

open import Examples.Groups.CCX+H.NaturalP.Schema
open import Examples.Groups.CCX+H.NaturalP.Theta using (θ)
open import Examples.Groups.CCX+H.NaturalP.Transfer using (θ-cong)
open import Examples.Groups.CCX+H.NaturalP.Elim using (elim ; elim′ ; Hp ; Hp-xor)
open import Examples.Groups.CCX+H.NaturalP.Soundness using (τH ; interpretH ; sound ; τH-θ)
import Examples.Groups.CCX+H.Presentation as T
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Par
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Bridge as PBr
import Examples.Groups.CCX+HH.NaturalP.EveryWidth as PE
import Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding as Emb

private
  variable
    m n : ℕ

open PB using (refl ; sym ; trans ; cong ; assoc ; right-unit)

-- The rules with the schema are complete on n wires.
Complete : ℕ → Set
Complete n = ∀ {u v : Circuit n} → interpretH u ≡ interpretH v → n ⊢ u ≈ v

------------------------------------------------------------------------
-- The parity of the number of H

private
  θ-even : (a : P.Circuit n) → Par.parity (τH (θ a)) ≡ false
  θ-even {n} a = Eq.trans
    (Par.physical-sound {u = τH (θ a)} {v = Emb.embed (PBr.τ a)} (T.sound n (τH-θ a)))
    (Par.expanded (PBr.τ a))

  Hp-parity : ∀ p → Par.parity (τH (Hp {m} p)) ≡ p
  Hp-parity false = Eq.refl
  Hp-parity true  = Eq.refl

  parity-of : (a : P.Circuit (₁₊ m)) (p : Bool) → Par.parity (τH (θ a • Hp p)) ≡ p
  parity-of a p = Eq.cong₂ _xor_ (θ-even a) (Hp-parity p)

  same-bit : ∀ (a b : P.Circuit (₁₊ m)) p q →
    interpretH (θ a • Hp p) ≡ interpretH (θ b • Hp q) → p ≡ q
  same-bit a b p q eq = Eq.trans (Eq.sym (parity-of a p))
    (Eq.trans (Par.physical-sound {u = τH (θ a • Hp p)} {v = τH (θ b • Hp q)} eq)
      (parity-of b q))

  Hp² : ∀ p → (₁₊ m) ⊢ Hp p • Hp p ≈ ε
  Hp² false = Hp-xor false false
  Hp² true  = Hp-xor true true

  cancel : ∀ (a b : P.Circuit (₁₊ m)) p →
    interpretH (θ a • Hp p) ≡ interpretH (θ b • Hp p) → interpretH (θ a) ≡ interpretH (θ b)
  cancel {m} a b p eq = Eq.trans (sound (sym (un a)))
    (Eq.trans (Eq.cong (_·*· interpretH {₁₊ m} (Hp p)) eq) (sound (un b)))
    where
    un : ∀ (c : P.Circuit (₁₊ m)) → (₁₊ m) ⊢ (θ c • Hp p) • Hp p ≈ θ c
    un c = trans assoc (trans (cong refl (Hp² p)) right-unit)

------------------------------------------------------------------------
-- Completeness

private
  finish : ∀ {u v : Circuit (₄₊ n)} (a b : P.Circuit (₄₊ n)) p →
    (₄₊ n) ⊢ u ≈ θ a • Hp p → (₄₊ n) ⊢ v ≈ θ b • Hp p →
    interpretH (θ a) ≡ interpretH (θ b) → PE.Complete (₄₊ n) → (₄₊ n) ⊢ u ≈ v
  finish {n} a b p e₁ e₂ eq pc =
    trans e₁ (trans (cong (θ-cong (pc {a} {b} (Emb.reflect {u = PBr.τ a} {v = PBr.τ b} eq′))) refl)
      (sym e₂))
    where
    eq′ : T.interpret (Emb.embed (PBr.τ a)) ≡ T.interpret (Emb.embed (PBr.τ b))
    eq′ = Eq.trans (Eq.sym (T.sound (₄₊ n) (τH-θ a))) (Eq.trans eq (T.sound (₄₊ n) (τH-θ b)))

complete-at : ∀ n → PE.Complete (₄₊ n) → Complete (₄₊ n)
complete-at n pc {u} {v} eq with elim u | elim v
... | elim′ a p e₁ | elim′ b q e₂ =
  finish a b p e₁ e₂′ (cancel a b p (Eq.trans (Eq.sym (sound e₁)) (Eq.trans eq (sound e₂′)))) pc
  where
  pq : p ≡ q
  pq = same-bit a b p q (Eq.trans (Eq.sym (sound e₁)) (Eq.trans eq (sound e₂)))
  e₂′ : (₄₊ n) ⊢ v ≈ θ b • Hp p
  e₂′ = Eq.subst (λ r → (₄₊ n) ⊢ v ≈ θ b • Hp r) (Eq.sym pq) e₂

-- From twelve wires of CCX+HH to every width from four on.
from-twelve : (∀ {n} → n ≤ 12 → PE.Complete n) → ∀ n → Complete (₄₊ n)
from-twelve h n = complete-at n (PE.every-width h (₄₊ n))

-- And to every width, given the widths up to three.
every-width : (∀ {n} → n ≤ 12 → PE.Complete n) → (∀ {n} → n ≤ 3 → Complete n) →
              ∀ n → Complete n
every-width h low n with n NP.≤? 3
... | yes le = low le
... | no gt  = Eq.subst Complete (NP.m+[n∸m]≡n {4} {n} (NP.≰⇒> gt)) (from-twelve h (n ∸ 4))
