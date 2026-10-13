------------------------------------------------------------------------
-- The exact three-coset Schreier table for X,CX,HH on two wires.
-- Generated from two_qubit_schreier.json by build_two_qubit_agda.py.
-- The state obligations below are Agda proofs, not external certificates.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.TwoQubit.Table where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (s≤s)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Decidable using (recompute)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Word.Base using (Word ; ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
open import Examples.Groups.CCX+HH.Encoding using (e)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.Schreier as Schreier

data Coset : Set where
  c0 c1 c2 : Coset

emit : Coset → T.Gen 4 → Circuit 2
emit c0 (T.M-gen ₀) = ε
emit c0 (T.M-gen ₁) = (X ↑) • HH • (X ↑) • HH • (X ↑)
emit c0 (T.M-gen ₂) = X • HH • X • HH • X
emit c0 (T.M-gen ₃) = X • HH • X • (X ↑) • HH • X
emit c0 (T.X-gen ₀ ₁ p) = X • CX
emit c0 (T.X-gen ₀ ₂ p) = (X ↑) • HH • CX • HH
emit c0 (T.X-gen ₀ ₃ p) = CX • (X ↑) • HH • CX • HH • CX
emit c0 (T.X-gen ₁ ₂ p) = CX • HH • CX • HH • CX
emit c0 (T.X-gen ₁ ₃ p) = HH • CX • HH
emit c0 (T.X-gen ₂ ₃ p) = CX
emit c0 (T.K-gen a b c d p q r) = HH
emit c1 (T.M-gen ₀) = ε
emit c1 (T.M-gen ₁) = (X ↑) • HH • (X ↑) • HH • (X ↑)
emit c1 (T.M-gen ₂) = X • HH • X • HH • X
emit c1 (T.M-gen ₃) = X • HH • X • (X ↑) • HH • X
emit c1 (T.X-gen ₀ ₁ p) = (X ↑) • CX • HH • (X ↑) • HH • (X ↑)
emit c1 (T.X-gen ₀ ₂ p) = X • HH • X • CX • HH • X
emit c1 (T.X-gen ₀ ₃ p) = X • CX • HH • X • CX • HH • X • CX
emit c1 (T.X-gen ₁ ₂ p) = CX • HH • CX • HH • CX
emit c1 (T.X-gen ₁ ₃ p) = HH • CX • HH
emit c1 (T.X-gen ₂ ₃ p) = CX
emit c1 (T.K-gen a b c d p q r) = ε
emit c2 (T.M-gen ₀) = CX • HH • CX • HH • CX • HH
emit c2 (T.M-gen ₁) = (X ↑) • CX • HH • CX • (X ↑) • HH • CX • HH
emit c2 (T.M-gen ₂) = X • CX • HH • (X ↑) • CX • HH • CX • HH
emit c2 (T.M-gen ₃) = CX • (X ↑) • HH • X • CX • HH • CX • HH
emit c2 (T.X-gen ₀ ₁ p) = HH • X • CX • HH
emit c2 (T.X-gen ₀ ₂ p) = CX • HH • (X ↑) • HH
emit c2 (T.X-gen ₀ ₃ p) = CX • HH • X • CX • HH • CX
emit c2 (T.X-gen ₁ ₂ p) = CX • HH • CX • HH • CX
emit c2 (T.X-gen ₁ ₃ p) = CX
emit c2 (T.X-gen ₂ ₃ p) = HH • CX • HH
emit c2 (T.K-gen a b c d p q r) = ε

-- Remaining X cases have impossible order proofs; the total fallback
-- keeps the table definition independent of proof irrelevance.
emit _ (T.X-gen _ _ _) = ε

step : Coset → T.Gen 4 → Coset
step c0 (T.M-gen _) = c1
step c1 (T.M-gen _) = c0
step c2 (T.M-gen _) = c2
step c (T.X-gen _ _ _) = c
step c0 (T.K-gen _ _ _ _ _ _ _) = c0
step c1 (T.K-gen _ _ _ _ _ _ _) = c2
step c2 (T.K-gen _ _ _ _ _ _ _) = c1

h : Coset → T.Gen 4 → Circuit 2 × Coset
h c g = emit c g , step c g

module Theory = Schreier 2 Coset c0 h
open Theory public using (decode ; state ; _===_ ; _≈_ ; roundtrip ; translated)

state-roundtrip : (g : Gen 2) → c0 ≡ state c0 (e g)
state-roundtrip (gate₀ ())
state-roundtrip X-gen = refl
state-roundtrip CX-gen = refl
state-roundtrip HH-gen = refl
state-roundtrip ((gate₀ ()) ↥)
state-roundtrip (X-gen ↥) = refl
state-roundtrip (((gate₀ ()) ↥) ↥)

full4 : (a b c d : Fin 4) → a < b → b < c → c < d →
          a ≡ ₀ × b ≡ ₁ × c ≡ ₂ × d ≡ ₃
full4 ₀ ₀ _ _ () _ _
full4 ₁ ₀ _ _ () _ _
full4 ₁ ₁ _ _ (s≤s ()) _ _
full4 ₂ ₀ _ _ () _ _
full4 ₂ ₁ _ _ (s≤s ()) _ _
full4 ₂ ₂ _ _ (s≤s (s≤s ())) _ _
full4 ₃ ₀ _ _ () _ _
full4 ₃ ₁ _ _ (s≤s ()) _ _
full4 ₃ ₂ _ _ (s≤s (s≤s ())) _ _
full4 ₃ ₃ _ _ (s≤s (s≤s (s≤s ()))) _ _
full4 _ ₀ ₀ _ _ () _
full4 _ ₁ ₀ _ _ () _
full4 _ ₁ ₁ _ _ (s≤s ()) _
full4 _ ₂ ₀ _ _ () _
full4 _ ₂ ₁ _ _ (s≤s ()) _
full4 _ ₂ ₂ _ _ (s≤s (s≤s ())) _
full4 _ ₃ ₀ _ _ () _
full4 _ ₃ ₁ _ _ (s≤s ()) _
full4 _ ₃ ₂ _ _ (s≤s (s≤s ())) _
full4 _ ₃ ₃ _ _ (s≤s (s≤s (s≤s ()))) _
full4 _ _ ₀ ₀ _ _ ()
full4 _ _ ₁ ₀ _ _ ()
full4 _ _ ₁ ₁ _ _ (s≤s ())
full4 _ _ ₂ ₀ _ _ ()
full4 _ _ ₂ ₁ _ _ (s≤s ())
full4 _ _ ₂ ₂ _ _ (s≤s (s≤s ()))
full4 _ _ ₃ ₀ _ _ ()
full4 _ _ ₃ ₁ _ _ (s≤s ())
full4 _ _ ₃ ₂ _ _ (s≤s (s≤s ()))
full4 _ _ ₃ ₃ _ _ (s≤s (s≤s (s≤s ())))

full4 ₀ ₁ ₂ ₃ _ _ _ = refl , refl , refl , refl

no-outside : (a b c d e : Fin 4) → b < c → c < d → d < e →
               a ≢ b → a ≢ c → a ≢ d → a ≢ e → ⊥
no-outside a b c d e p q r ab ac ad ae with full4 b c d e p q r
no-outside ₀ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ab refl
no-outside ₁ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ac refl
no-outside ₂ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ad refl
no-outside ₃ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ae refl

state-relations : ∀ c {u v} → u T.=== v → state c u ≡ state c v
state-relations c0 (T.r1a _) = refl
state-relations c1 (T.r1a _) = refl
state-relations c2 (T.r1a _) = refl
state-relations c0 T.r1b = refl
state-relations c1 T.r1b = refl
state-relations c2 T.r1b = refl
state-relations c0 (T.r1c _ _ _) = refl
state-relations c1 (T.r1c _ _ _) = refl
state-relations c2 (T.r1c _ _ _) = refl
state-relations c0 (T.r2a _ _ _ _ _ _) = refl
state-relations c1 (T.r2a _ _ _ _ _ _) = refl
state-relations c2 (T.r2a _ _ _ _ _ _) = refl
state-relations c0 (T.r2b _ _ _) = refl
state-relations c1 (T.r2b _ _ _) = refl
state-relations c2 (T.r2b _ _ _) = refl
state-relations c0 (T.r2c _ _ _ _ _ _ _ _ _ _ _ _) = refl
state-relations c1 (T.r2c _ _ _ _ _ _ _ _ _ _ _ _) = refl
state-relations c2 (T.r2c _ _ _ _ _ _ _ _ _ _ _ _) = refl
state-relations c0 (T.r2d _) = refl
state-relations c1 (T.r2d _) = refl
state-relations c2 (T.r2d _) = refl
state-relations c0 (T.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl
state-relations c1 (T.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl
state-relations c2 (T.r2f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl
state-relations c0 (T.r3a _ _ _) = refl
state-relations c1 (T.r3a _ _ _) = refl
state-relations c2 (T.r3a _ _ _) = refl
state-relations c0 (T.r3b _ _ _) = refl
state-relations c1 (T.r3b _ _ _) = refl
state-relations c2 (T.r3b _ _ _) = refl
state-relations c0 (T.r3c _) = refl
state-relations c1 (T.r3c _) = refl
state-relations c2 (T.r3c _) = refl
state-relations c0 (T.r3d _ _ _ _ _) = refl
state-relations c1 (T.r3d _ _ _ _ _) = refl
state-relations c2 (T.r3d _ _ _ _ _) = refl
state-relations c0 (T.r3e _ _ _ _ _ _) = refl
state-relations c1 (T.r3e _ _ _ _ _ _) = refl
state-relations c2 (T.r3e _ _ _ _ _ _) = refl
state-relations c0 (T.r3f _ _ _ _ _ _) = refl
state-relations c1 (T.r3f _ _ _ _ _ _) = refl
state-relations c2 (T.r3f _ _ _ _ _ _) = refl
state-relations c0 (T.r3g _ _ _ _ _) = refl
state-relations c1 (T.r3g _ _ _ _ _) = refl
state-relations c2 (T.r3g _ _ _ _ _) = refl
state-relations c0 (T.r4a _ _ _ _) = refl
state-relations c1 (T.r4a _ _ _ _) = refl
state-relations c2 (T.r4a _ _ _ _) = refl
state-relations c0 (T.r4b _ _ _) = refl
state-relations c1 (T.r4b _ _ _) = refl
state-relations c2 (T.r4b _ _ _) = refl
state-relations c0 (T.r4c _ _ _ _) = refl
state-relations c1 (T.r4c _ _ _ _) = refl
state-relations c2 (T.r4c _ _ _ _) = refl
state-relations c0 (T.r5a _ _ _ _ _ _ _) = refl
state-relations c1 (T.r5a _ _ _ _ _ _ _) = refl
state-relations c2 (T.r5a _ _ _ _ _ _ _) = refl
state-relations c0 (T.r6a _ _ _ _ _ _ _ _) = refl
state-relations c1 (T.r6a _ _ _ _ _ _ _ _) = refl
state-relations c2 (T.r6a _ _ _ _ _ _ _ _) = refl
state-relations z (T.r2e {b = b} {c = c} {d = d} {e = e} {a = a} p q r ab ac ad ae) =
  ⊥-elim (no-outside a b c d e (recompute (b FP.<? c) p)
    (recompute (c FP.<? d) q) (recompute (d FP.<? e) r) ab ac ad ae)

open Theory.Complete state-roundtrip state-relations public using (encoded-completeness)
