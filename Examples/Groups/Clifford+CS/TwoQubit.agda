------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-qubit completeness (the analogue of Clément, Section 7.2)
--
-- On two qubits the circuits denote all of U₄(ℤ[½,i]) — CS has
-- determinant i, so there is no parity obstruction — and the auxiliary
-- language is the whole of the two-level one: words over the one- and
-- two-level matrices on four basis vectors, with the complete theory of
-- Bian and Selinger (Clifford+CS-TwoLevel, through Bridge).  This
-- module is the two-qubit instance of BackAndForth:
--
--   * the encoding E on the generators — a gate on a wire is the
--     product of its one- or two-level copies over the other wire's
--     basis — and that it preserves the semantics, by computation;
--   * the decoding D, a table of sixteen circuits: the phase i_[a] is
--     CS with its controls negated where a has a 0; X_[a,b] is a CNOT,
--     the swap, or the swap with both wires negated; K_[a,b] is a
--     controlled K (Bian and Selinger's CK₀₁ and CK₁₀) with negated
--     control, or conjugated by a CNOT when a and b differ in both bits;
--   * completeness, from the completeness of the two-level relations
--     and the two lemmas that the paper proves in its Appendix C for
--     the real case: D respects the relations (Lemma 7.5) and inverts E
--     (Lemma 7.4).  They are the parameters of Lemma-7-6 below.
--
-- Basis vectors are indexed 0 … 3 with wire 0 the most significant bit:
-- k = 2 x₀ + x₁.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.TwoQubit where

open import Data.Fin using (Fin ; zero ; suc ; _<_)
import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; ~-sym)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+CS.Bridge as Bridge
import Examples.Groups.Clifford+CS.TwoLevelTries as TwoLevelTries

module T = Bridge.TwoLevel 2
private
  module TT = TwoLevelTries 2

------------------------------------------------------------------------
-- The four indices

private
  0<1 : _<_ {4} {4} ₀ ₁
  0<1 = ℕ.s≤s ℕ.z≤n
  0<2 : _<_ {4} {4} ₀ ₂
  0<2 = ℕ.s≤s ℕ.z≤n
  1<3 : _<_ {4} {4} ₁ ₃
  1<3 = ℕ.s≤s (ℕ.s≤s ℕ.z≤n)
  2<3 : _<_ {4} {4} ₂ ₃
  2<3 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))

------------------------------------------------------------------------
-- The encoding

e : Gen 2 → Word (TL.Gen 4)
e I-gen         = TL.i ₀ • TL.i ₁ • TL.i ₂ • TL.i ₃
e (I-gen ↥)     = TL.i ₀ • TL.i ₁ • TL.i ₂ • TL.i ₃
e (I-gen ↥ ↥)   = TL.i ₀ • TL.i ₁ • TL.i ₂ • TL.i ₃
e S-gen         = TL.i ₂ • TL.i ₃
e K-gen         = TL.K ₀ ₂ 0<2 • TL.K ₁ ₃ 1<3
e CS-gen        = TL.i ₃
e (S-gen ↥)     = TL.i ₁ • TL.i ₃
e (K-gen ↥)     = TL.K ₀ ₁ 0<1 • TL.K ₂ ₃ 2<3

-- It preserves the semantics, by computation.
e-sem : ∀ g → T.⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
e-sem g = ~-sym {s = ⟦ [ g ]ʷ ⟧} {T.⟦ e g ⟧Y} (TT.by-same [ g ]ʷ (e g) (ok g))
  where
  ok : ∀ g → TT.Same [ g ]ʷ (e g)
  ok I-gen       = refl
  ok (I-gen ↥)   = refl
  ok (I-gen ↥ ↥) = refl
  ok S-gen       = refl
  ok K-gen       = refl
  ok CS-gen      = refl
  ok (S-gen ↥)   = refl
  ok (K-gen ↥)   = refl

------------------------------------------------------------------------
-- The decoding

-- X on wire 1, and the controlled K gates of Bian and Selinger: K on
-- wire 1 controlled by wire 0 (CK₀₁, the two-level K_[2,3]), and on
-- wire 0 controlled by wire 1 (CK₁₀, K_[1,3]).
X↑ : Circuit 2
X↑ = X ↑

CK₀₁ CK₁₀ : Circuit 2
CK₀₁ = CS • K ↑ • CS • K ↑ • CS • S • S • S • iI
CK₁₀ = CS • K • CS • K • CS • S ↑ • S ↑ • S ↑ • iI

d : TL.Gen 4 → Circuit 2
-- The phase i on |a⟩.
d (TL.i-gen ₃) = CS
d (TL.i-gen ₂) = X↑ • CS • X↑
d (TL.i-gen ₁) = X • CS • X
d (TL.i-gen ₀) = X • X↑ • CS • X • X↑
-- The exchange of |a⟩ and |b⟩.
d (TL.X-gen ₂ ₃ _) = CX₀₁
d (TL.X-gen ₀ ₁ _) = X • CX₀₁ • X
d (TL.X-gen ₁ ₃ _) = CX₁₀
d (TL.X-gen ₀ ₂ _) = X↑ • CX₁₀ • X↑
d (TL.X-gen ₁ ₂ _) = Swap
d (TL.X-gen ₀ ₃ _) = Swap • X • X↑
-- K on the span of |a⟩ and |b⟩.
d (TL.K-gen ₂ ₃ _) = CK₀₁
d (TL.K-gen ₀ ₁ _) = X • CK₀₁ • X
d (TL.K-gen ₁ ₃ _) = CK₁₀
d (TL.K-gen ₀ ₂ _) = X↑ • CK₁₀ • X↑
d (TL.K-gen ₁ ₂ _) = CX₀₁ • CK₁₀ • CX₀₁
d (TL.K-gen ₀ ₃ _) = CX₁₀ • X • CK₀₁ • X • CX₁₀
-- No letter has a ≥ b; these never occur.
d (TL.X-gen _ _ _) = ε
d (TL.K-gen _ _ _) = ε

------------------------------------------------------------------------
-- Two-qubit completeness (the analogue of Lemma 7.6)

-- Lemma 7.4: the decoding inverts the encoding, on the generators.
Lemma-7-4 : Set
Lemma-7-4 = ∀ g → 2 ⊢ [ g ]ʷ ≈ (d ʷ) (e g)

-- Lemma 7.5: the decoding respects the relations on four indices.
Lemma-7-5 : Set
Lemma-7-5 = ∀ {u t} → TL._===_ {4} u t → 2 ⊢ (d ʷ) u ≈ (d ʷ) t

module Lemma-7-6 (lemma-7-4 : Lemma-7-4) (lemma-7-5 : Lemma-7-5) where
  open T.BF.Complete T.complete-Y e e-sem d lemma-7-5 lemma-7-4 public using (complete)
