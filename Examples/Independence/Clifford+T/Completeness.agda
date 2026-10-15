------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffT₂ is complete for the matrix semantics on at most two wires
-- (Theorem 22(4), by transfer)
--
-- Section 4 of Blake's paper.  On two wires the transfer is from Bian
-- and Selinger's presentation of the 2-qubit Clifford+T group
-- (Examples.Groups.Clifford+T-2qubit, complete over 𝔻[ω]); on one wire
-- and on none, from the two-level presentation of U₂(𝔻[ω]) and
-- U₁(𝔻[ω]) (Examples.Groups.Clifford+T-2qubit-TwoLevel).  The
-- encodings (Clifford+T.Bridge) send a circuit to words whose matrix
-- is the circuit's (or, for Bian and Selinger's, its transpose), so
-- circuits with equal matrices have encodings equal by those
-- presentations' rules.  The decodings send their words back: Bian and
-- Selinger's as written, S as T T and CZ as H CNOT H on wire 0; the
-- two-level ones read backwards, ω_[0] as ω T†, ω_[1] as T, X_[0,1] as
-- X and H_[0,1] as H (a generator on equal indices, which the
-- relations never meet, as ε).  Every rule decodes to a derivation of
-- CliffT₂'s (Lemma 20: Clifford+T.Derivations; that ω is central is
-- Central-Scalars'), so equal encodings have equal decodings; and
-- decoding the encoding gives the circuit back (Lemma 19: back₀,
-- back₁, back₂).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.Completeness where

open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (ℕ ; z≤n ; s≤s ; _≤_)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_ ; _,_)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainLemma as TLM
open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
import Examples.Groups.Clifford+T-2qubit.Presentation as BSP

open import Examples.Independence.Clifford+T.Syntactics
import Examples.Independence.Clifford+T.Semantics as Sem
open import Examples.Independence.Clifford+T.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf ; ω⁸⁼)
open import Examples.Independence.Clifford+T.Derivations
open import Examples.Independence.Clifford+T.Bridge using (ℰ₀ ; ℰ₁ ; ℰ₂ ; module V₀ ; module V₁ ; module V₂)
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (lift)

module BS = Clifford+T

private
  variable
    n : ℕ

  one : (h h' : PGate 0) → h ≡ h'
  one ⌈ ω-gate ⌉ ⌈ ω-gate ⌉ = refl

open Single-Scalar one using (comm-gate₀-w)

------------------------------------------------------------------------
-- Reading an equation of letter lists between words

private
  via : {w v : Circuit n} (e : Eqn n) →
        Assoc.to-list (n VRel,_===_) w ≡ Assoc.to-list (n VRel,_===_) ⟪ lhs⁼ e ⟫ →
        Assoc.to-list (n VRel,_===_) ⟪ rhs⁼ e ⟫ ≡ Assoc.to-list (n VRel,_===_) v →
        n ⊢ w ≈ v
  via {n} e p q =
    PB.trans (PP.by-assoc (n VRel,_===_) p) (PB.trans (prf e) (PP.by-assoc (n VRel,_===_) q))

  -- A word of another presentation, decoded letter by letter and read
  -- backwards.
  module Decode {G : Set} (d : G → Circuit n) where

    Dʷ : Word G → Circuit n
    Dʷ [ g ]ʷ  = d g
    Dʷ ε       = ε
    Dʷ (w • v) = Dʷ v • Dʷ w

    -- Every derivation of a relation whose axioms decode to
    -- derivations.
    module _ {Γ : Word G → Word G → Set} (D-rel : ∀ {w v} → Γ w v → n ⊢ Dʷ w ≈ Dʷ v) where

      D-≈ : ∀ {w v} → PB._≈_ Γ w v → n ⊢ Dʷ w ≈ Dʷ v
      D-≈ PB.refl        = PB.refl
      D-≈ (PB.sym e)     = PB.sym (D-≈ e)
      D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
      D-≈ (PB.cong e f)  = PB.cong (D-≈ f) (D-≈ e)
      D-≈ PB.assoc       = PB.sym PB.assoc
      D-≈ PB.left-unit   = PB.right-unit
      D-≈ PB.right-unit  = PB.left-unit
      D-≈ (PB.axiom a)   = D-rel a

  -- ... and read as written.
  module DecodeF {G : Set} (d : G → Circuit n) where

    Dʷ : Word G → Circuit n
    Dʷ [ g ]ʷ  = d g
    Dʷ ε       = ε
    Dʷ (w • v) = Dʷ w • Dʷ v

    module _ {Γ : Word G → Word G → Set} (D-rel : ∀ {w v} → Γ w v → n ⊢ Dʷ w ≈ Dʷ v) where

      D-≈ : ∀ {w v} → PB._≈_ Γ w v → n ⊢ Dʷ w ≈ Dʷ v
      D-≈ PB.refl        = PB.refl
      D-≈ (PB.sym e)     = PB.sym (D-≈ e)
      D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
      D-≈ (PB.cong e f)  = PB.cong (D-≈ e) (D-≈ f)
      D-≈ PB.assoc       = PB.assoc
      D-≈ PB.left-unit   = PB.left-unit
      D-≈ PB.right-unit  = PB.right-unit
      D-≈ (PB.axiom a)   = D-rel a

------------------------------------------------------------------------
-- Indices of the two-level generators in dimensions 1 and 2

private
  ¬<0 : ∀ {m} → ¬ (ℕ.suc m ≤ 0)
  ¬<0 ()

  ¬2≤1 : ¬ (2 ≤ 1)
  ¬2≤1 (s≤s ())

  -- In dimension 2, a < b only for a = 0 and b = 1.
  lt2 : (a b : Fin 2) → .(a < b) → a ≡ zero × b ≡ suc zero
  lt2 zero       zero       p = Irr.⊥-elim (¬<0 p)
  lt2 zero       (suc zero) p = refl , refl
  lt2 (suc zero) zero       p = Irr.⊥-elim (¬<0 p)
  lt2 (suc zero) (suc zero) p = Irr.⊥-elim (¬2≤1 p)

  -- ... so never 1 < b.
  no1< : (b : Fin 2) → .(suc (zero {0}) < b) → ⊥
  no1< zero       p = Irr.⊥-elim (¬<0 p)
  no1< (suc zero) p = Irr.⊥-elim (¬2≤1 p)

  -- ... and an index is 0 or 1.
  nz : (j : Fin 2) → j ≢ zero → j ≢ suc zero → ⊥
  nz zero       a b = a refl
  nz (suc zero) a b = b refl

  -- In dimension 1, never a < b.
  lt1 : (a b : Fin 1) → .(a < b) → ⊥
  lt1 zero zero p = Irr.⊥-elim (¬<0 p)

------------------------------------------------------------------------
-- No wire: the two-level presentation in dimension 1

d₀ : TL.Gen 1 → Circuit 0
d₀ (TL.i-gen zero)   = ω
d₀ (TL.X-gen _ _ _)  = ε
d₀ (TL.K-gen _ _ _)  = ε

open Decode d₀ renaming (Dʷ to D₀ʷ ; D-≈ to D₀-≈)

D₀-rel : ∀ {w v} → w TL.=== v → 0 ⊢ D₀ʷ w ≈ D₀ʷ v
D₀-rel (TL.order-ω {j = zero}) = via ω⁸⁼ refl refl
D₀-rel (TL.order-H {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.order-X {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.comm-ωω {j = zero} {k = zero} ne) = ⊥-elim (ne refl)
D₀-rel (TL.comm-ωH {k = k} {l = l} p _ _) = ⊥-elim (lt1 k l p)
D₀-rel (TL.comm-ωX {k = k} {l = l} p _ _) = ⊥-elim (lt1 k l p)
D₀-rel (TL.comm-HH {j = j} {k = k} p _ _ _ _ _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.comm-HX {j = j} {k = k} p _ _ _ _ _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.comm-XX {j = j} {k = k} p _ _ _ _ _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-Xω {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-Xω′ {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-XX {j = j} {k = k} p _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-XX′ {j = j} {k = k} _ q) = ⊥-elim (lt1 j k q)
D₀-rel (TL.swap-XH {j = j} {k = k} p _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-XH′ {j = j} {k = k} _ q) = ⊥-elim (lt1 j k q)
D₀-rel (TL.scalar-X {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.scalar-H {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-18 {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-19 {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-20 {j = j} {k = k} p _ _) = ⊥-elim (lt1 j k p)

back₀ : (w : Circuit 0) → 0 ⊢ D₀ʷ (V₀.ℰʷ w) ≈ w
back₀ [ gate₀ ⌈ ω-gate ⌉ ]ʷ = PB.refl
back₀ ε                     = PB.refl
back₀ (w • v)               = PB.cong (back₀ w) (back₀ v)

------------------------------------------------------------------------
-- One wire: the two-level presentation in dimension 2

d₁ : TL.Gen 2 → Circuit 1
d₁ (TL.i-gen zero)                = ω • T†
d₁ (TL.i-gen (suc zero))          = T
d₁ (TL.X-gen zero (suc zero) _)   = X
d₁ (TL.X-gen _ _ _)               = ε
d₁ (TL.K-gen zero (suc zero) _)   = H
d₁ (TL.K-gen _ _ _)               = ε

open Decode d₁ renaming (Dʷ to D₁ʷ ; D-≈ to D₁-≈)

D₁-rel : ∀ {w v} → w TL.=== v → 1 ⊢ D₁ʷ w ≈ D₁ʷ v
D₁-rel (TL.order-ω {j = zero})       = via DTL-order-ω₀⁼ refl refl
D₁-rel (TL.order-ω {j = suc zero})   = via DTL-order-ω₁⁼ refl refl
D₁-rel (TL.order-H {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-order-H⁼ refl refl
D₁-rel (TL.order-X {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-order-X⁼ refl refl
D₁-rel (TL.comm-ωω {j = zero} {k = zero} ne)          = ⊥-elim (ne refl)
D₁-rel (TL.comm-ωω {j = zero} {k = suc zero} ne)     = via DTL-comm-ωω⁼ refl refl
D₁-rel (TL.comm-ωω {j = suc zero} {k = zero} ne)     = via DTL-comm-ωω′⁼ refl refl
D₁-rel (TL.comm-ωω {j = suc zero} {k = suc zero} ne) = ⊥-elim (ne refl)
D₁-rel (TL.comm-ωH {k = k} {l = l} {j = j} p jk jl) with lt2 k l p
... | refl , refl = ⊥-elim (nz j jk jl)
D₁-rel (TL.comm-ωX {k = k} {l = l} {j = j} p jk jl) with lt2 k l p
... | refl , refl = ⊥-elim (nz j jk jl)
D₁-rel (TL.comm-HH {j = j} {k = k} {l = l} {m = m} p q jl _ _ _) with lt2 j k p | lt2 l m q
... | refl , refl | refl , refl = ⊥-elim (jl refl)
D₁-rel (TL.comm-HX {j = j} {k = k} {l = l} {m = m} p q jl _ _ _) with lt2 j k p | lt2 l m q
... | refl , refl | refl , refl = ⊥-elim (jl refl)
D₁-rel (TL.comm-XX {j = j} {k = k} {l = l} {m = m} p q jl _ _ _) with lt2 j k p | lt2 l m q
... | refl , refl | refl , refl = ⊥-elim (jl refl)
D₁-rel (TL.swap-Xω {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-swap-Xω⁼ refl refl
D₁-rel (TL.swap-Xω′ {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-swap-Xω′⁼ refl refl
D₁-rel (TL.swap-XX {j = j} {k = k} {l = l} p q) with lt2 j k p
... | refl , refl = ⊥-elim (no1< l q)
D₁-rel (TL.swap-XX′ {l = l} {j = j} {k = k} p q) with lt2 l j p
... | refl , refl = ⊥-elim (no1< k q)
D₁-rel (TL.swap-XH {j = j} {k = k} {l = l} p q) with lt2 j k p
... | refl , refl = ⊥-elim (no1< l q)
D₁-rel (TL.swap-XH′ {l = l} {j = j} {k = k} p q) with lt2 l j p
... | refl , refl = ⊥-elim (no1< k q)
D₁-rel (TL.scalar-X {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-scalar-X⁼ refl refl
D₁-rel (TL.scalar-H {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-scalar-H⁼ refl refl
D₁-rel (TL.rel-18 {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-rel-18⁼ refl refl
D₁-rel (TL.rel-19 {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL-rel-19⁼ refl refl
D₁-rel (TL.rel-20 {j = j} {k = k} {l = l} p q _) with lt2 j k p
... | refl , refl = ⊥-elim (no1< l q)

back₁-gen : (g : Gen 1) → 1 ⊢ D₁ʷ (ℰ₁ g) ≈ [ g ]ʷ
back₁-gen (gate₀ ⌈ ω-gate ⌉)   = via Dω₁⁼ refl refl
back₁-gen (gate₁ ⌈ H-gate ⌉)   = PB.refl
back₁-gen (gate₁ ⌈ T-gate ⌉)   = PB.refl
back₁-gen (gate₀ ⌈ ω-gate ⌉ ↥) =
  PB.trans (via Dω₁⁼ refl refl) (PB.sym (PB.axiom (ω↑=ω ⌈ ω-gate ⌉)))

back₁ : (w : Circuit 1) → 1 ⊢ D₁ʷ (V₁.ℰʷ w) ≈ w
back₁ [ g ]ʷ  = back₁-gen g
back₁ ε       = PB.refl
back₁ (w • v) = PB.cong (back₁ w) (back₁ v)

------------------------------------------------------------------------
-- Two wires: Bian and Selinger's presentation

d₂ : BS.Generator → Circuit 2
d₂ BS.W-gen  = ω
d₂ BS.H0-gen = H
d₂ BS.H1-gen = H ↑
d₂ BS.S0-gen = S
d₂ BS.S1-gen = S ↑
d₂ BS.T0-gen = T
d₂ BS.T1-gen = T ↑
d₂ BS.CZ-gen = H • CX • H

open DecodeF d₂ renaming (Dʷ to D₂ʷ ; D-≈ to D₂-≈)

D₂-rel : ∀ {w v} → BS.Rel w v → 2 ⊢ D₂ʷ w ≈ D₂ʷ v
D₂-rel (BS.comm-W g)        = PB.sym (comm-gate₀-w ⌈ ω-gate ⌉ (d₂ g))
D₂-rel BS.comm-H0-H1        = via DBS-comm-H0-H1⁼ refl refl
D₂-rel BS.comm-H0-S1        = via DBS-comm-H0-S1⁼ refl refl
D₂-rel BS.comm-H0-T1        = via DBS-comm-H0-T1⁼ refl refl
D₂-rel BS.comm-S0-H1        = via DBS-comm-S0-H1⁼ refl refl
D₂-rel BS.comm-S0-S1        = via DBS-comm-S0-S1⁼ refl refl
D₂-rel BS.comm-S0-T1        = via DBS-comm-S0-T1⁼ refl refl
D₂-rel BS.comm-T0-H1        = via DBS-comm-T0-H1⁼ refl refl
D₂-rel BS.comm-T0-S1        = via DBS-comm-T0-S1⁼ refl refl
D₂-rel BS.comm-T0-T1        = via DBS-comm-T0-T1⁼ refl refl
D₂-rel BS.order-W           = via DBS-order-W⁼ refl refl
D₂-rel BS.order-H0          = via DBS-order-H0⁼ refl refl
D₂-rel BS.order-H1          = via DBS-order-H1⁼ refl refl
D₂-rel BS.order-S0          = via DBS-order-S0⁼ refl refl
D₂-rel BS.order-S1          = via DBS-order-S1⁼ refl refl
D₂-rel BS.order-S0H0        = via DBS-order-S0H0⁼ refl refl
D₂-rel BS.order-S1H1        = via DBS-order-S1H1⁼ refl refl
D₂-rel BS.order-CZ          = via DBS-order-CZ⁼ refl refl
D₂-rel BS.comm-S0-CZ        = via DBS-comm-S0-CZ⁼ refl refl
D₂-rel BS.comm-S1-CZ        = via DBS-comm-S1-CZ⁼ refl refl
D₂-rel BS.rel-X0-CZ         = via DBS-rel-X0-CZ⁼ refl refl
D₂-rel BS.rel-X1-CZ         = via DBS-rel-X1-CZ⁼ refl refl
D₂-rel BS.rel-CZ-H0-CZ      = via DBS-rel-CZ-H0-CZ⁼ refl refl
D₂-rel BS.rel-CZ-H1-CZ      = via DBS-rel-CZ-H1-CZ⁼ refl refl
D₂-rel BS.square-T0         = via DBS-square-T0⁼ refl refl
D₂-rel BS.square-T1         = via DBS-square-T1⁼ refl refl
D₂-rel BS.lemma-order-T0X0  = via DBS-lemma-order-T0X0⁼ refl refl
D₂-rel BS.lemma-order-T1X1  = via DBS-lemma-order-T1X1⁼ refl refl
D₂-rel BS.comm-T0-CZ        = via DBS-comm-T0-CZ⁼ refl refl
D₂-rel BS.swap-T0           = via DBS-swap-T0⁼ refl refl
D₂-rel BS.rel-A             = via DBS-rel-A⁼ refl refl
D₂-rel BS.rel-B             = via DBS-rel-B⁼ refl refl
D₂-rel BS.rel-C             = via DBS-rel-C⁼ refl refl

back₂-gen : (g : Gen 2) → 2 ⊢ D₂ʷ (ℰ₂ g) ≈ [ g ]ʷ
back₂-gen (gate₀ ⌈ ω-gate ⌉)     = PB.refl
back₂-gen (gate₁ ⌈ H-gate ⌉)     = PB.refl
back₂-gen (gate₁ ⌈ T-gate ⌉)     = PB.refl
back₂-gen (gate₂ ⌈ CX-gate ⌉)    = via DCX⁼ refl refl
back₂-gen (gate₂ swap)           = via Dσ⁼ refl refl
back₂-gen (gate₀ ⌈ ω-gate ⌉ ↥)   = PB.sym (PB.axiom (ω↑=ω ⌈ ω-gate ⌉))
back₂-gen (gate₁ ⌈ H-gate ⌉ ↥)   = PB.refl
back₂-gen (gate₁ ⌈ T-gate ⌉ ↥)   = PB.refl
back₂-gen (gate₀ ⌈ ω-gate ⌉ ↥ ↥) =
  PB.trans (PB.sym (PB.axiom (ω↑=ω ⌈ ω-gate ⌉))) (lift (PB.sym (PB.axiom (ω↑=ω ⌈ ω-gate ⌉))))

back₂ : (w : Circuit 2) → 2 ⊢ D₂ʷ (V₂.ℰʷ w) ≈ w
back₂ [ g ]ʷ  = back₂-gen g
back₂ ε       = PB.refl
back₂ (w • v) = PB.cong (back₂ w) (back₂ v)

------------------------------------------------------------------------
-- Completeness

private
  complete₀ : {w v : Circuit 0} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 0 ⊢ w ≈ v
  complete₀ {w} {v} e =
    PB.trans (PB.sym (back₀ w))
      (PB.trans (D₀-≈ D₀-rel (TLM.relations-complete {n = 1} (s≤s z≤n)
                                {V₀.ℰʷ w} {V₀.ℰʷ v} (V₀.transfer {w} {v} e)))
                (back₀ v))

  complete₁ : {w v : Circuit 1} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 1 ⊢ w ≈ v
  complete₁ {w} {v} e =
    PB.trans (PB.sym (back₁ w))
      (PB.trans (D₁-≈ D₁-rel (TLM.relations-complete {n = 2} (s≤s (s≤s z≤n))
                                {V₁.ℰʷ w} {V₁.ℰʷ v} (V₁.transfer {w} {v} e)))
                (back₁ v))

  complete₂ : {w v : Circuit 2} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 2 ⊢ w ≈ v
  complete₂ {w} {v} e =
    PB.trans (PB.sym (back₂ w))
      (PB.trans (D₂-≈ D₂-rel (BSP.complete {V₂.ℰʷ w} {V₂.ℰʷ v} (V₂.transfer {w} {v} e)))
                (back₂ v))

-- Circuits on at most two wires with the same matrix are equal by
-- CliffT₂.
complete : n ≤ 2 → {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
complete z≤n             = complete₀
complete (s≤s z≤n)       = complete₁
complete (s≤s (s≤s z≤n)) = complete₂

-- So on at most two wires the rule set presents the semantics.
sound-complete : n ≤ 2 → {w v : Circuit n} → (n ⊢ w ≈ v) ⇔ (Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧)
sound-complete n≤2 = mk⇔ Sem.sound (complete n≤2)
