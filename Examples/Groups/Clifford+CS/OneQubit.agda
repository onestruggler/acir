------------------------------------------------------------------------
-- Presentations of groups
--
-- One-qubit completeness
--
-- The back-and-forth argument with the one- and two-level words on two
-- indices, whose complete theory is that of Bian and Selinger
-- (Clifford+CS-TwoLevel, through Bridge):
--
--   * the encoding sends S to i_[1] (the phase on |1⟩), K to K_[0,1],
--     and the scalar to i_[0] i_[1];
--   * the decoding sends i_[1] to S, i_[0] to X S X (the phase on |0⟩),
--     X_[0,1] to X and K_[0,1] to K, with X = K S² K iI;
--   * that the decoding respects the relations on two indices, and
--     inverts the encoding, are equations on one wire, derived in
--     Lemmas.OneWire.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.OneQubit where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
import Data.Nat as ℕ
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; ~-sym)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Derivation (1 VRel,_===_) using (⌈_⌉)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+CS.Bridge as Bridge
import Examples.Groups.Clifford+CS.TwoLevelTries as TwoLevelTries
import Examples.Groups.Clifford+CS.Lemmas.OneWire as OneWire

module T = Bridge.TwoLevel 1

private
  module TT = TwoLevelTries 1
  module W  = OneWire {0}

------------------------------------------------------------------------
-- Two indices

f0 f1 : Fin 2
f0 = zero
f1 = suc zero

0<1 : f0 < f1
0<1 = ℕ.s≤s ℕ.z≤n

private
  -- Two ordered indices are 0 and 1.
  rc : {a b : Fin 2} → .(a < b) → a < b
  rc {a} {b} p = recompute (a FinP.<? b) p

  lt : {a b : Fin 2} → a < b → (a ≡ f0) × (b ≡ f1)
  lt {zero}     {suc zero} _              = refl , refl
  lt {suc zero} {suc zero} (ℕ.s≤s ())

  -- So no index is below 0, none above 1, and there is no third.
  ¬<0 : {a : Fin 2} → .(a < f0) → ⊥
  ¬<0 {a} p with lt {a} {f0} (rc {a} {f0} p)
  ... | _ , ()

  ¬1< : {b : Fin 2} → .(f1 < b) → ⊥
  ¬1< {b} p with lt {f1} {b} (rc {f1} {b} p)
  ... | () , _

  third : (j k l : Fin 2) → .(k < l) → j ≢ k → j ≢ l → ⊥
  third j k l p jk jl with lt {k} {l} (rc {k} {l} p)
  third zero     .zero .(suc zero) p jk jl | refl , refl = jk refl
  third (suc zero) .zero .(suc zero) p jk jl | refl , refl = jl refl

  chain : {j k l : Fin 2} → j < k → k < l → ⊥
  chain {j} {k} {l} p q with lt {j} {k} p | lt {k} {l} q
  ... | _ , refl | () , _

------------------------------------------------------------------------
-- The encoding and the decoding

e : Gen 1 → Word (TL.Gen 2)
e I-gen       = TL.i f0 • TL.i f1
e S-gen       = TL.i f1
e K-gen       = TL.K f0 f1 0<1
e (I-gen ↥)   = TL.i f0 • TL.i f1

d : TL.Gen 2 → Circuit 1
d (TL.i-gen zero)       = X • S • X
d (TL.i-gen (suc zero)) = S
d (TL.X-gen _ _ _)      = X
d (TL.K-gen _ _ _)      = K

d∘e : ∀ g → 1 ⊢ [ g ]ʷ ≈ (d ʷ) (e g)
d∘e I-gen     = ⌈ PB.sym W.XSXS ⌉
d∘e S-gen     = PB.refl
d∘e K-gen     = PB.refl
d∘e (I-gen ↥) = PB.trans (PB.axiom (ω↑=ω I-gate)) ⌈ PB.sym W.XSXS ⌉

e-sem : ∀ g → T.⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
e-sem g = ~-sym {s = ⟦ [ g ]ʷ ⟧} {T.⟦ e g ⟧Y} (by g (ok g))
  where
  by : ∀ g → TT.Same [ g ]ʷ (e g) → ⟦ [ g ]ʷ ⟧ ~ T.⟦ e g ⟧Y
  by g = TT.by-same [ g ]ʷ (e g)
  ok : ∀ g → TT.Same [ g ]ʷ (e g)
  ok I-gen     = refl
  ok S-gen     = refl
  ok K-gen     = refl
  ok (I-gen ↥) = refl

------------------------------------------------------------------------
-- The decoding respects the relations on two indices

d-wd : ∀ {u t} → TL._===_ {2} u t → 1 ⊢ (d ʷ) u ≈ (d ʷ) t
d-wd (TL.order-i {j = zero})                    = ⌈ W.XSX⁴ ⌉
d-wd (TL.order-i {j = suc zero})                = PB.axiom (srel order-S)
d-wd (TL.order-X p)                             = ⌈ W.XX ⌉
d-wd (TL.order-K p)                             = ⌈ W.K⁸ ⌉
d-wd (TL.comm-ii {j = zero}     {k = suc zero} _) = ⌈ W.XSX-S ⌉
d-wd (TL.comm-ii {j = suc zero} {k = zero}     _) = ⌈ PB.sym W.XSX-S ⌉
d-wd (TL.comm-ii {j = zero}     {k = zero}     jk) = ⊥-elim (jk refl)
d-wd (TL.comm-ii {j = suc zero} {k = suc zero} jk) = ⊥-elim (jk refl)
d-wd (TL.comm-iX {k = k} {l = l} {j = j} p jk jl) = ⊥-elim (third j k l p jk jl)
d-wd (TL.comm-iK {k = k} {l = l} {j = j} p jk jl) = ⊥-elim (third j k l p jk jl)
d-wd (TL.comm-XX {j = j} {k = k} {l = l} p q jl jm kl km) =
  ⊥-elim (third l j k p (λ e → jl (Eq.sym e)) (λ e → kl (Eq.sym e)))
d-wd (TL.comm-XK {j = j} {k = k} {l = l} p q jl jm kl km) =
  ⊥-elim (third l j k p (λ e → jl (Eq.sym e)) (λ e → kl (Eq.sym e)))
d-wd (TL.comm-KK {j = j} {k = k} {l = l} p q jl jm kl km) =
  ⊥-elim (third l j k p (λ e → jl (Eq.sym e)) (λ e → kl (Eq.sym e)))
d-wd (TL.swap-iX {j = zero} {k = suc zero} p)   = ⌈ W.S-X ⌉
d-wd (TL.swap-iX {j = j} {k = zero} p)          = ⊥-elim (¬<0 {j} p)
d-wd (TL.swap-iX {j = suc zero} {k = k} p)      = ⊥-elim (¬1< {k} p)
d-wd (TL.swap-XX p q)                           = ⊥-elim (chain p q)
d-wd (TL.swap-XX′ p q)                          = ⊥-elim (chain p q)
d-wd (TL.swap-KX p q)                           = ⊥-elim (chain p q)
d-wd (TL.swap-KX′ p q)                          = ⊥-elim (chain p q)
d-wd (TL.rel-13 {j = j} {k = suc zero} p)       = ⌈ W.K-Z ⌉
d-wd (TL.rel-13 {j = j} {k = zero} p)           = ⊥-elim (¬<0 {j} p)
d-wd (TL.rel-14 {j = j} {k = suc zero} p)       = ⌈ W.K-S³ ⌉
d-wd (TL.rel-14 {j = j} {k = zero} p)           = ⊥-elim (¬<0 {j} p)
d-wd (TL.rel-15 {j = zero} {k = suc zero} p)    = ⌈ W.K-XSXS ⌉
d-wd (TL.rel-15 {j = j} {k = zero} p)           = ⊥-elim (¬<0 {j} p)
d-wd (TL.rel-15 {j = suc zero} {k = k} p)       = ⊥-elim (¬1< {k} p)
d-wd (TL.rel-16 {j = zero} {k = suc zero} p)    = ⌈ W.K²XSXS ⌉
d-wd (TL.rel-16 {j = j} {k = zero} p)           = ⊥-elim (¬<0 {j} p)
d-wd (TL.rel-16 {j = suc zero} {k = k} p)       = ⊥-elim (¬1< {k} p)
d-wd (TL.rel-17 {j = j} {k = k} {l = l} jk lm jl km k≢l) with lt {j} {k} (rc {j} {k} jk) | lt {j} {l} (rc {j} {l} jl)
... | refl , refl | refl , refl = ⊥-elim (k≢l refl)

------------------------------------------------------------------------
-- One-qubit completeness

open T.BF.Complete T.complete-Y e e-sem d d-wd d∘e public using (complete)
