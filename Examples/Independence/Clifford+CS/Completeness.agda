------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂ is complete for the matrix semantics on at most three
-- wires (Theorem 22(5), by transfer)
--
-- Section 4 of Blake's paper.  On three wires the transfer is from Bian
-- and Selinger's presentation of the 3-qubit Clifford+CS group
-- (Examples.Groups.Clifford+CS-3qubit); on two wires, one and none,
-- from the two-level presentation of U₄, U₂ and U₁ over 𝔻[i] = ℤ[½,i]
-- (Examples.Groups.Clifford+CS-TwoLevel).  Their scalars are the
-- powers of i, ours those of ω: the encodings (Clifford+CS.Encodings)
-- count the ω of a circuit (H = ω K), and Clifford+CS.Assemble does the
-- rest.  The decodings read the source words as written: iI, resp. the
-- scalar i on an index, as ω ω, K as ω† H, S and CS as themselves; on
-- one wire the two-level i_[1] as S, i_[0] as ω ω S†, X_[0,1] as X (a
-- generator on equal indices, which the relations never meet, as ε);
-- on two wires each two-level generator as a conjugate of CS, of a
-- controlled K or of a CNOT by X, the swap and the CNOT
-- (Clifford+CS.TwoWire).  Every relation decodes to a derivation of
-- CliffCS₂'s (Lemma 20: Clifford+CS.Derivations, and on two wires one
-- instance of each relation, the others by transport along the
-- permutations of the indices), and every gate is ω^c times the
-- decoding of its encoding (Lemma 19).  Two-wire derivations use the
-- axioms of arity at most two only, so the two-wire case is not a
-- consequence of the three-wire one.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Completeness where

open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (ℕ ; z≤n ; s≤s ; _≤_)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_ ; _,_)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

import Examples.Groups.Clifford+CS-TwoLevel.Ring as CSR
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+CS-TwoLevel.Semantics as CSS
import Examples.Groups.Clifford+CS-TwoLevel.MainLemma as TLM
import Examples.Groups.Clifford+CS-3qubit.Presentation as BSP

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Sem
open import Examples.Independence.Clifford+CS.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf ; lift⁼ ; ω⁸⁼)
open import Examples.Independence.Clifford+CS.Derivations
open import Examples.Independence.Clifford+CS.Bridge using (mapι ; ωs ; scalar-word)
open import Examples.Independence.Clifford+CS.Encodings
open import Examples.Independence.Clifford+CS.Assemble
import Examples.Independence.Clifford+CS.TwoWire as TW
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (lift)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Reading an equation of letter lists between words

private
  via : {w v : Circuit n} (e : Eqn n) →
        Assoc.to-list (n VRel,_===_) w ≡ Assoc.to-list (n VRel,_===_) ⟪ lhs⁼ e ⟫ →
        Assoc.to-list (n VRel,_===_) ⟪ rhs⁼ e ⟫ ≡ Assoc.to-list (n VRel,_===_) v →
        n ⊢ w ≈ v
  via {n} e p q =
    PB.trans (PP.by-assoc (n VRel,_===_) p) (PB.trans (prf e) (PP.by-assoc (n VRel,_===_) q))

  -- X is ω times ω† X.
  ω-back : (X : Circuit n) → n ⊢ X ≈ ω • (ω† • X)
  ω-back X = PB.sym (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong ωᵏ⁸ PB.refl) PB.left-unit))

  -- The scalar word decodes to i times.
  FJ : ∀ {m} {G : Set} (F : Word G → Matrix m m CSR.D) →
       (∀ u v → F (u • v) ≡ F u ·*· F v) → (J : Word G) →
       mapι (F J) ≡ ωs 2 (mapι CSS.𝕀) → ∀ u → mapι (F (J • u)) ≡ ωs 2 (mapι (F u))
  FJ F F-• J h u = Eq.trans (Eq.cong mapι (F-• J u)) (scalar-word (F J) (F u) h)

  -- ω one wire up is ω.
  ω↑ : ℕ.suc n ⊢ [ gate₀ ⌈ ω-gate ⌉ ↥ ]ʷ ≈ ω
  ω↑ = PB.axiom (ω↑=ω ⌈ ω-gate ⌉)

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
d₀ (TL.i-gen zero)  = ω • ω
d₀ (TL.X-gen _ _ _) = ε
d₀ (TL.K-gen _ _ _) = ε

module W₀ = Assemble CSS.⟦_⟧ᵐ refl CSS.⟦•⟧ᵐ CSS.Unitary-⟦⟧ᵐ J₀
  (FJ CSS.⟦_⟧ᵐ CSS.⟦•⟧ᵐ J₀ J₀-i) ℰ₀ c₀ gen₀
  TL._===_ (TLM.relations-complete {n = 1}) d₀

D₀-rel : ∀ {w v} → w TL.=== v → 0 ⊢ W₀.Dʷ w ≈ W₀.Dʷ v
D₀-rel (TL.order-i {j = zero}) = via ω⁸⁼ refl refl
D₀-rel (TL.order-X {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.order-K {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.comm-ii {j = zero} {k = zero} ne) = ⊥-elim (ne refl)
D₀-rel (TL.comm-iX {k = k} {l = l} p _ _) = ⊥-elim (lt1 k l p)
D₀-rel (TL.comm-iK {k = k} {l = l} p _ _) = ⊥-elim (lt1 k l p)
D₀-rel (TL.comm-XX {j = j} {k = k} p _ _ _ _ _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.comm-XK {j = j} {k = k} p _ _ _ _ _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.comm-KK {j = j} {k = k} p _ _ _ _ _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-iX {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-XX {j = j} {k = k} p _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-XX′ {j = j} {k = k} p _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-KX {j = j} {k = k} p _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.swap-KX′ {j = j} {k = k} p _) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-13 {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-14 {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-15 {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-16 {j = j} {k = k} p) = ⊥-elim (lt1 j k p)
D₀-rel (TL.rel-17 {j = j} {k = k} p _ _ _ _) = ⊥-elim (lt1 j k p)

back₀ : (g : Gen 0) → 0 ⊢ [ g ]ʷ ≈ ωᵏ (c₀ g) • W₀.Dʷ (ℰ₀ g)
back₀ (gate₀ ⌈ ω-gate ⌉) = PB.sym PB.right-unit

complete₀ : {w v : Circuit 0} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 0 ⊢ w ≈ v
complete₀ = W₀.complete D₀-rel PB.refl back₀

------------------------------------------------------------------------
-- One wire: the two-level presentation in dimension 2

d₁ : TL.Gen 2 → Circuit 1
d₁ (TL.i-gen zero)              = ω • ω • S†
d₁ (TL.i-gen (suc zero))        = S
d₁ (TL.X-gen zero (suc zero) _) = X
d₁ (TL.X-gen _ _ _)             = ε
d₁ (TL.K-gen zero (suc zero) _) = ω† • H
d₁ (TL.K-gen _ _ _)             = ε

module W₁ = Assemble CSS.⟦_⟧ᵐ refl CSS.⟦•⟧ᵐ CSS.Unitary-⟦⟧ᵐ J₁
  (FJ CSS.⟦_⟧ᵐ CSS.⟦•⟧ᵐ J₁ J₁-i) ℰ₁ c₁ gen₁
  TL._===_ (TLM.relations-complete {n = 2}) d₁

D₁-rel : ∀ {w v} → w TL.=== v → 1 ⊢ W₁.Dʷ w ≈ W₁.Dʷ v
D₁-rel (TL.order-i {j = zero})     = via DTL1-order-i-0⁼ refl refl
D₁-rel (TL.order-i {j = suc zero}) = via DTL1-order-i-1⁼ refl refl
D₁-rel (TL.order-X {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL1-order-X-01⁼ refl refl
D₁-rel (TL.order-K {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL1-order-K-01⁼ refl refl
D₁-rel (TL.comm-ii {j = zero} {k = zero} ne)          = ⊥-elim (ne refl)
D₁-rel (TL.comm-ii {j = zero} {k = suc zero} ne)     = via DTL1-comm-ii-01⁼ refl refl
D₁-rel (TL.comm-ii {j = suc zero} {k = zero} ne)     = via DTL1-comm-ii-10⁼ refl refl
D₁-rel (TL.comm-ii {j = suc zero} {k = suc zero} ne) = ⊥-elim (ne refl)
D₁-rel (TL.comm-iX {k = k} {l = l} {j = j} p jk jl) with lt2 k l p
... | refl , refl = ⊥-elim (nz j jk jl)
D₁-rel (TL.comm-iK {k = k} {l = l} {j = j} p jk jl) with lt2 k l p
... | refl , refl = ⊥-elim (nz j jk jl)
D₁-rel (TL.comm-XX {j = j} {k = k} {l = l} {m = m} p q jl _ _ _) with lt2 j k p | lt2 l m q
... | refl , refl | refl , refl = ⊥-elim (jl refl)
D₁-rel (TL.comm-XK {j = j} {k = k} {l = l} {m = m} p q jl _ _ _) with lt2 j k p | lt2 l m q
... | refl , refl | refl , refl = ⊥-elim (jl refl)
D₁-rel (TL.comm-KK {j = j} {k = k} {l = l} {m = m} p q jl _ _ _) with lt2 j k p | lt2 l m q
... | refl , refl | refl , refl = ⊥-elim (jl refl)
D₁-rel (TL.swap-iX {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL1-swap-iX-01⁼ refl refl
D₁-rel (TL.swap-XX {j = j} {k = k} {l = l} p q) with lt2 j k p
... | refl , refl = ⊥-elim (no1< l q)
D₁-rel (TL.swap-XX′ {j = j} {k = k} {l = l} p q) with lt2 j k p
... | refl , refl = ⊥-elim (no1< l q)
D₁-rel (TL.swap-KX {j = j} {k = k} {l = l} p q) with lt2 j k p
... | refl , refl = ⊥-elim (no1< l q)
D₁-rel (TL.swap-KX′ {j = j} {k = k} {l = l} p q) with lt2 j k p
... | refl , refl = ⊥-elim (no1< l q)
D₁-rel (TL.rel-13 {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL1-rel-13-01⁼ refl refl
D₁-rel (TL.rel-14 {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL1-rel-14-01⁼ refl refl
D₁-rel (TL.rel-15 {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL1-rel-15-01⁼ refl refl
D₁-rel (TL.rel-16 {j = j} {k = k} p) with lt2 j k p
... | refl , refl = via DTL1-rel-16-01⁼ refl refl
D₁-rel (TL.rel-17 {j = j} {k = k} {l = l} {m = m} jk _ _ km _) with lt2 j k jk
... | refl , refl = ⊥-elim (no1< m km)

back₁ : (g : Gen 1) → 1 ⊢ [ g ]ʷ ≈ ωᵏ (c₁ g) • W₁.Dʷ (ℰ₁ g)
back₁ (gate₀ ⌈ ω-gate ⌉)   = PB.sym PB.right-unit
back₁ (gate₁ ⌈ H-gate ⌉)   = ω-back H
back₁ (gate₁ ⌈ S-gate ⌉)   = PB.sym PB.left-unit
back₁ (gate₀ ⌈ ω-gate ⌉ ↥) = PB.trans ω↑ (PB.sym PB.right-unit)

complete₁ : {w v : Circuit 1} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 1 ⊢ w ≈ v
complete₁ = W₁.complete D₁-rel (via DJ1⁼ refl refl) back₁

------------------------------------------------------------------------
-- Two wires: the two-level presentation in dimension 4

module W₂ = Assemble CSS.⟦_⟧ᵐ refl CSS.⟦•⟧ᵐ CSS.Unitary-⟦⟧ᵐ J₂
  (FJ CSS.⟦_⟧ᵐ CSS.⟦•⟧ᵐ J₂ J₂-i) ℰ₂ c₂ gen₂
  TL._===_ (TLM.relations-complete {n = 4}) TW.d₂

back₂ : (g : Gen 2) → 2 ⊢ [ g ]ʷ ≈ ωᵏ (c₂ g) • W₂.Dʷ (ℰ₂ g)
back₂ (gate₀ ⌈ ω-gate ⌉)     = PB.sym PB.right-unit
back₂ (gate₁ ⌈ H-gate ⌉)     = via DH2⁼ refl refl
back₂ (gate₁ ⌈ S-gate ⌉)     = PB.trans (via DS2⁼ refl refl) (PB.sym PB.left-unit)
back₂ (gate₂ ⌈ CS-gate ⌉)    = PP.by-assoc (2 VRel,_===_) refl
back₂ (gate₂ swap)           = PB.trans (via DSW2⁼ refl refl) (PB.sym PB.left-unit)
back₂ (gate₀ ⌈ ω-gate ⌉ ↥)   = PB.trans ω↑ (PB.sym PB.right-unit)
back₂ (gate₁ ⌈ H-gate ⌉ ↥)   = via DH2↑⁼ refl refl
back₂ (gate₁ ⌈ S-gate ⌉ ↥)   = PB.trans (via DS2↑⁼ refl refl) (PB.sym PB.left-unit)
back₂ (gate₀ ⌈ ω-gate ⌉ ↥ ↥) = PB.trans (lift ω↑) (PB.trans ω↑ (PB.sym PB.right-unit))

complete₂ : {w v : Circuit 2} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 2 ⊢ w ≈ v
complete₂ = W₂.complete TW.D₂-rel (via DJ2⁼ refl refl) back₂

------------------------------------------------------------------------
-- Three wires: Bian and Selinger's presentation

d₃ : BS.Gen → Circuit 3
d₃ BS.S0-gen   = S
d₃ BS.S1-gen   = S ↑
d₃ BS.S2-gen   = S ↑ ↑
d₃ BS.CS01-gen = CS
d₃ BS.CS12-gen = CS ↑
d₃ BS.iI-gen   = ω • ω
d₃ BS.K0-gen   = ω† • H
d₃ BS.K1-gen   = ω† • H ↑
d₃ BS.K2-gen   = ω† • H ↑ ↑

F₃-• : ∀ u v → F₃ (u • v) ≡ F₃ u ·*· F₃ v
F₃-• u v = CSS.⟦•⟧ᵐ ((BSP.tl ʷ) u) ((BSP.tl ʷ) v)

module W₃ = Assemble F₃ refl F₃-• (λ u → CSS.Unitary-⟦⟧ᵐ ((BSP.tl ʷ) u)) J₃
  (FJ F₃ F₃-• J₃ J₃-i) ℰ₃ c₃ gen₃
  BS.Rel (λ {u} {v} → BSP.complete {u} {v}) d₃

D₃-rel : ∀ {w v} → BS.Rel w v → 3 ⊢ W₃.Dʷ w ≈ W₃.Dʷ v
D₃-rel BS.ax-iI-iI-iI-iI=ε = via DBS-iI-iI-iI-iI=ε⁼ refl refl
D₃-rel BS.ax-iI-S0=S0-iI = via DBS-iI-S0=S0-iI⁼ refl refl
D₃-rel BS.ax-iI-S1=S1-iI = via DBS-iI-S1=S1-iI⁼ refl refl
D₃-rel BS.ax-iI-S2=S2-iI = via DBS-iI-S2=S2-iI⁼ refl refl
D₃-rel BS.ax-iI-K0=K0-iI = via DBS-iI-K0=K0-iI⁼ refl refl
D₃-rel BS.ax-iI-K1=K1-iI = via DBS-iI-K1=K1-iI⁼ refl refl
D₃-rel BS.ax-iI-K2=K2-iI = via DBS-iI-K2=K2-iI⁼ refl refl
D₃-rel BS.ax-iI-CS01=CS01-iI = via DBS-iI-CS01=CS01-iI⁼ refl refl
D₃-rel BS.ax-iI-CS12=CS12-iI = via DBS-iI-CS12=CS12-iI⁼ refl refl
D₃-rel BS.ax-S1-S0=S0-S1 = via DBS-S1-S0=S0-S1⁼ refl refl
D₃-rel BS.ax-S2-S0=S0-S2 = via DBS-S2-S0=S0-S2⁼ refl refl
D₃-rel BS.ax-S2-S1=S1-S2 = via DBS-S2-S1=S1-S2⁼ refl refl
D₃-rel BS.ax-K1-K0=K0-K1 = via DBS-K1-K0=K0-K1⁼ refl refl
D₃-rel BS.ax-K2-K0=K0-K2 = via DBS-K2-K0=K0-K2⁼ refl refl
D₃-rel BS.ax-K2-K1=K1-K2 = via DBS-K2-K1=K1-K2⁼ refl refl
D₃-rel BS.ax-CS01-S0=S0-CS01 = via DBS-CS01-S0=S0-CS01⁼ refl refl
D₃-rel BS.ax-CS12-S0=S0-CS12 = via DBS-CS12-S0=S0-CS12⁼ refl refl
D₃-rel BS.ax-CS01-S1=S1-CS01 = via DBS-CS01-S1=S1-CS01⁼ refl refl
D₃-rel BS.ax-CS12-S1=S1-CS12 = via DBS-CS12-S1=S1-CS12⁼ refl refl
D₃-rel BS.ax-CS01-S2=S2-CS01 = via DBS-CS01-S2=S2-CS01⁼ refl refl
D₃-rel BS.ax-CS12-S2=S2-CS12 = via DBS-CS12-S2=S2-CS12⁼ refl refl
D₃-rel BS.ax-CS12-CS01=CS01-CS12 = via DBS-CS12-CS01=CS01-CS12⁼ refl refl
D₃-rel BS.ax-S1-K0=K0-S1 = via DBS-S1-K0=K0-S1⁼ refl refl
D₃-rel BS.ax-S2-K0=K0-S2 = via DBS-S2-K0=K0-S2⁼ refl refl
D₃-rel BS.ax-S2-K1=K1-S2 = via DBS-S2-K1=K1-S2⁼ refl refl
D₃-rel BS.ax-K1-S0=S0-K1 = via DBS-K1-S0=S0-K1⁼ refl refl
D₃-rel BS.ax-K2-S0=S0-K2 = via DBS-K2-S0=S0-K2⁼ refl refl
D₃-rel BS.ax-K2-S1=S1-K2 = via DBS-K2-S1=S1-K2⁼ refl refl
D₃-rel BS.ax-CS01-K2=K2-CS01 = via DBS-CS01-K2=K2-CS01⁼ refl refl
D₃-rel BS.ax-CS12-K0=K0-CS12 = via DBS-CS12-K0=K0-CS12⁼ refl refl
D₃-rel BS.ax-S0-S0-S0-S0=ε = via DBS-S0-S0-S0-S0=ε⁼ refl refl
D₃-rel BS.ax-S1-S1-S1-S1=ε = via DBS-S1-S1-S1-S1=ε⁼ refl refl
D₃-rel BS.ax-S2-S2-S2-S2=ε = via DBS-S2-S2-S2-S2=ε⁼ refl refl
D₃-rel BS.ax-CS01-CS01-CS01-CS01=ε = via DBS-CS01-CS01-CS01-CS01=ε⁼ refl refl
D₃-rel BS.ax-CS12-CS12-CS12-CS12=ε = via DBS-CS12-CS12-CS12-CS12=ε⁼ refl refl
D₃-rel BS.ax-K0-K0=iI-iI-iI = via DBS-K0-K0=iI-iI-iI⁼ refl refl
D₃-rel BS.ax-K1-K1=iI-iI-iI = via DBS-K1-K1=iI-iI-iI⁼ refl refl
D₃-rel BS.ax-K2-K2=iI-iI-iI = via DBS-K2-K2=iI-iI-iI⁼ refl refl
D₃-rel BS.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI = via DBS-S0-K0-S0-K0-S0-K0=iI-iI-iI⁼ refl refl
D₃-rel BS.ax-S1-K1-S1-K1-S1-K1=iI-iI-iI = via DBS-S1-K1-S1-K1-S1-K1=iI-iI-iI⁼ refl refl
D₃-rel BS.ax-S2-K2-S2-K2-S2-K2=iI-iI-iI = via DBS-S2-K2-S2-K2-S2-K2=iI-iI-iI⁼ refl refl
D₃-rel BS.ax-X0-CS01=CS01-CS01-CS01-X0-S1 = via DBS-X0-CS01=CS01-CS01-CS01-X0-S1⁼ refl refl
D₃-rel BS.ax-X1-CS01=CS01-CS01-CS01-X1-S0 = via DBS-X1-CS01=CS01-CS01-CS01-X1-S0⁼ refl refl
D₃-rel BS.ax-X1-CS12=CS12-CS12-CS12-X1-S2 = via DBS-X1-CS12=CS12-CS12-CS12-X1-S2⁼ refl refl
D₃-rel BS.ax-X2-CS12=CS12-CS12-CS12-X2-S1 = via DBS-X2-CS12=CS12-CS12-CS12-X2-S1⁼ refl refl
D₃-rel BS.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 = via DBS-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01⁼ refl refl
D₃-rel BS.ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01 = via DBS-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01⁼ refl refl
D₃-rel BS.ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12 = via DBS-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12⁼ refl refl
D₃-rel BS.ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12 = via DBS-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12⁼ refl refl
D₃-rel BS.ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12 = via DBS-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12⁼ refl refl
D₃-rel BS.ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12 = via DBS-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12⁼ refl refl
D₃-rel BS.ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21 = via DBS-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21⁼ refl refl
D₃-rel BS.ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12 = via DBS-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12⁼ refl refl
D₃-rel BS.ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1 = via DBS-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1⁼ refl refl

back₃ : (g : Gen 3) → 3 ⊢ [ g ]ʷ ≈ ωᵏ (c₃ g) • W₃.Dʷ (ℰ₃ g)
back₃ (gate₀ ⌈ ω-gate ⌉)       = PB.sym PB.right-unit
back₃ (gate₁ ⌈ H-gate ⌉)       = ω-back H
back₃ (gate₁ ⌈ S-gate ⌉)       = PB.sym PB.left-unit
back₃ (gate₂ ⌈ CS-gate ⌉)      = PB.sym PB.left-unit
back₃ (gate₂ swap)             = PB.trans (PB.sym (via DSwap⁼ refl refl)) (PB.sym PB.left-unit)
back₃ (gate₀ ⌈ ω-gate ⌉ ↥)     = PB.trans ω↑ (PB.sym PB.right-unit)
back₃ (gate₁ ⌈ H-gate ⌉ ↥)     = ω-back (H ↑)
back₃ (gate₁ ⌈ S-gate ⌉ ↥)     = PB.sym PB.left-unit
back₃ (gate₂ ⌈ CS-gate ⌉ ↥)    = PB.sym PB.left-unit
back₃ (gate₂ swap ↥)           =
  PB.trans (PB.sym (via (lift⁼ DSwap⁼) refl refl)) (PB.sym PB.left-unit)
back₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥)   = PB.trans (lift ω↑) (PB.trans ω↑ (PB.sym PB.right-unit))
back₃ (gate₁ ⌈ H-gate ⌉ ↥ ↥)   = ω-back (H ↑ ↑)
back₃ (gate₁ ⌈ S-gate ⌉ ↥ ↥)   = PB.sym PB.left-unit
back₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥ ↥) =
  PB.trans (lift (lift ω↑)) (PB.trans (lift ω↑) (PB.trans ω↑ (PB.sym PB.right-unit)))
back₃ (gate₃ ⌈ () ⌉)

complete₃ : {w v : Circuit 3} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 3 ⊢ w ≈ v
complete₃ = W₃.complete D₃-rel PB.refl back₃

------------------------------------------------------------------------
-- Completeness

-- Circuits on at most three wires with the same matrix are equal by
-- CliffCS₂.
complete : n ≤ 3 → {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
complete z≤n                   = complete₀
complete (s≤s z≤n)             = complete₁
complete (s≤s (s≤s z≤n))       = complete₂
complete (s≤s (s≤s (s≤s z≤n))) = complete₃

-- So on at most three wires the rule set presents the semantics.
sound-complete : n ≤ 3 → {w v : Circuit n} → (n ⊢ w ≈ v) ⇔ (Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧)
sound-complete n≤3 = mk⇔ Sem.sound (complete n≤3)
