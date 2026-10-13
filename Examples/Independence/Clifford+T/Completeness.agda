------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffT₂ is complete for the matrix semantics up to two qubits
-- (Theorem 22(4), by transfer)
--
-- Section 4 of Blake's paper.  On two wires, from Bian and Selinger's
-- presentation of 2-qubit Clifford+T operators (Examples.Groups.Clifford+
-- T-2qubit); on one wire, from Greylyn's presentation of U₂(ℤ[1/√2, i])
-- (Examples.Groups.Clifford+T-2qubit-TwoLevel at n = 2), which the paper
-- does not need to cite separately but a proof does, the 2-qubit
-- theorem saying nothing of one-wire circuits; on no wires, directly.
-- Both sources are complete for their matrices over 𝔻[ω].  The
-- encodings ℰʷ, ℰ₁ʷ send a circuit to their words, and the decodings
-- Dʷ, Dʷ₁ send their words back letter for letter (Clifford+T.Bridge);
-- every relation of theirs decodes to a derivation of CliffT₂'s
-- (Lemma 20: Clifford+T.Decodings, the paper's Appendix G.4 over its
-- Appendix D, and Greylyn's relations at n = 2), and decoding the
-- encoding gives the circuit back (Lemma 19: back, back₁).  Their
-- matrix of a word is the transpose of CliffT₂'s matrix of its decoding
-- (bridge₂, bridge₁), so two circuits with equal matrices have encodings
-- whose decodings, being derivably equal to them, have equal matrices:
-- the encodings are equal by their rules, and so the circuits by
-- CliffT₂'s.  On no wires a circuit is a power of ω, and ω has order 8.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.Completeness where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (tt)
import Data.Empty.Irrelevant as Irr
open import Data.Fin.Base as Fin using (Fin ; zero ; suc)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _+_ ; _*_ ; _%_ ; _/_ ; s≤s ; z≤n ; _≤_ ; _<_)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n ; m%n<n)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (proj₁)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
import Examples.Groups.Clifford+T-2qubit.Presentation as BS
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics as TLS
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainLemma {2} using (relations-complete)

open import Examples.Independence.Clifford+T.Syntactics
import Examples.Independence.Clifford+T.Semantics as Sem
import Examples.Independence.Semantics.Qubit as O
open import Examples.Independence.Clifford+T.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf ; ω⁸⁼)
open import Examples.Independence.Clifford+T.Decodings
open import Examples.Independence.Clifford+T.Bridge
  using (ℰ ; ℰʷ ; Dʷ ; ℰ₁ ; ℰ₁ʷ ; Dʷ₁ ; bridge₂ ; bridge₁ ; exact ; ᵀ-cong ; module QM)
import Examples.Independence.Reasoning Gate as R
open R.Theory arity lhs rhs using (lift)

open O.Circuits Sem.val using (module Exact)

module C = Clifford+T

private
  variable
    n : ℕ

  -- An equation of letter lists, read between words.
  via : {w v : Circuit n} (e : Eqn n) →
        Assoc.to-list (n VRel,_===_) w ≡ Assoc.to-list (n VRel,_===_) ⟪ lhs⁼ e ⟫ →
        Assoc.to-list (n VRel,_===_) ⟪ rhs⁼ e ⟫ ≡ Assoc.to-list (n VRel,_===_) v →
        n ⊢ w ≈ v
  via {n} e p q =
    PB.trans (PP.by-assoc (n VRel,_===_) p) (PB.trans (prf e) (PP.by-assoc (n VRel,_===_) q))

  -- Equal matrices of the decodings of their words.
  through : {w v : Circuit n} {w′ v′ : Circuit n} →
            n ⊢ w′ ≈ w → n ⊢ v′ ≈ v → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → Sem.⟦ w′ ⟧ Sem.≈ Sem.⟦ v′ ⟧
  through bw bv e = Exact.≈-trans (Sem.sound bw) (Exact.≈-trans e (Exact.≈-sym (Sem.sound bv)))

------------------------------------------------------------------------
-- Two wires

module Two where

  private
    variable
      w v : Word C.Generator

  -- Lemma 20: their relations, decoded, are derivable.
  D-rel : C.Rel w v → 2 ⊢ Dʷ w ≈ Dʷ v
  D-rel (C.comm-W C.W-gen) = via DcommWW⁼ refl refl
  D-rel (C.comm-W C.H0-gen) = via DcommWH0⁼ refl refl
  D-rel (C.comm-W C.H1-gen) = via DcommWH1⁼ refl refl
  D-rel (C.comm-W C.S0-gen) = via DcommWS0⁼ refl refl
  D-rel (C.comm-W C.S1-gen) = via DcommWS1⁼ refl refl
  D-rel (C.comm-W C.T0-gen) = via DcommWT0⁼ refl refl
  D-rel (C.comm-W C.T1-gen) = via DcommWT1⁼ refl refl
  D-rel (C.comm-W C.CZ-gen) = via DcommWCZ⁼ refl refl
  D-rel C.comm-H0-H1 = via DcommH0H1⁼ refl refl
  D-rel C.comm-H0-S1 = via DcommH0S1⁼ refl refl
  D-rel C.comm-H0-T1 = via DcommH0T1⁼ refl refl
  D-rel C.comm-S0-H1 = via DcommS0H1⁼ refl refl
  D-rel C.comm-S0-S1 = via DcommS0S1⁼ refl refl
  D-rel C.comm-S0-T1 = via DcommS0T1⁼ refl refl
  D-rel C.comm-T0-H1 = via DcommT0H1⁼ refl refl
  D-rel C.comm-T0-S1 = via DcommT0S1⁼ refl refl
  D-rel C.comm-T0-T1 = via DcommT0T1⁼ refl refl
  D-rel C.order-W = via DorderW⁼ refl refl
  D-rel C.order-H0 = via DorderH0⁼ refl refl
  D-rel C.order-H1 = via DorderH1⁼ refl refl
  D-rel C.order-S0 = via DorderS0⁼ refl refl
  D-rel C.order-S1 = via DorderS1⁼ refl refl
  D-rel C.order-S0H0 = via DorderS0H0⁼ refl refl
  D-rel C.order-S1H1 = via DorderS1H1⁼ refl refl
  D-rel C.order-CZ = via DorderCZ⁼ refl refl
  D-rel C.comm-S0-CZ = via DcommS0CZ⁼ refl refl
  D-rel C.comm-S1-CZ = via DcommS1CZ⁼ refl refl
  D-rel C.rel-X0-CZ = via DrelX0CZ⁼ refl refl
  D-rel C.rel-X1-CZ = via DrelX1CZ⁼ refl refl
  D-rel C.rel-CZ-H0-CZ = via DrelCZH0CZ⁼ refl refl
  D-rel C.rel-CZ-H1-CZ = via DrelCZH1CZ⁼ refl refl
  D-rel C.lemma-order-T0X0 = via DlemmaorderT0X0⁼ refl refl
  D-rel C.lemma-order-T1X1 = via DlemmaorderT1X1⁼ refl refl
  D-rel C.comm-T0-CZ = via DcommT0CZ⁼ refl refl
  D-rel C.swap-T0 = via DswapT0⁼ refl refl
  D-rel C.rel-A = via DrelA⁼ refl refl
  D-rel C.rel-B = via DrelB⁼ refl refl
  D-rel C.rel-C = via DrelC⁼ refl refl
  D-rel C.square-T0 = PB.refl
  D-rel C.square-T1 = PB.refl

  -- So every derivation of theirs.
  D-≈ : PB._≈_ C.Rel w v → 2 ⊢ Dʷ w ≈ Dʷ v
  D-≈ PB.refl        = PB.refl
  D-≈ (PB.sym e)     = PB.sym (D-≈ e)
  D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
  D-≈ (PB.cong e f)  = PB.cong (D-≈ e) (D-≈ f)
  D-≈ PB.assoc       = PB.assoc
  D-≈ PB.left-unit   = PB.left-unit
  D-≈ PB.right-unit  = PB.right-unit
  D-≈ (PB.axiom a)   = D-rel a

  -- Lemma 19: decoding the encoding.
  private
    ω↑ : 2 ⊢ ω ↑ ≈ ω
    ω↑ = PB.axiom (ω↑=ω ⌈ ω-gate ⌉)

    ω↑↑ : 2 ⊢ ω ↑ ↑ ≈ ω
    ω↑↑ = PB.trans (lift (PB.axiom (ω↑=ω ⌈ ω-gate ⌉))) ω↑

  back-gen : (g : Gen 2) → 2 ⊢ Dʷ (ℰ g) ≈ [ g ]ʷ
  back-gen (gate₀ ⌈ ω-gate ⌉)       = PB.refl
  back-gen (gate₁ ⌈ H-gate ⌉)       = PB.refl
  back-gen (gate₁ ⌈ T-gate ⌉)       = PB.refl
  back-gen (gate₂ ⌈ CX-gate ⌉)      = via DCX⁼ refl refl
  back-gen (gate₂ swap)             = via Dσ⁼ refl refl
  back-gen (gate₀ ⌈ ω-gate ⌉ ↥)     = PB.sym ω↑
  back-gen (gate₁ ⌈ H-gate ⌉ ↥)     = PB.refl
  back-gen (gate₁ ⌈ T-gate ⌉ ↥)     = PB.refl
  back-gen ((gate₀ ⌈ ω-gate ⌉ ↥) ↥) = PB.sym ω↑↑

  back : (w : Circuit 2) → 2 ⊢ Dʷ (ℰʷ w) ≈ w
  back [ g ]ʷ  = back-gen g
  back ε       = PB.refl
  back (w • v) = PB.cong (back w) (back v)

  complete : {w v : Circuit 2} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 2 ⊢ w ≈ v
  complete {w} {v} e =
    PB.trans (PB.sym (back w)) (PB.trans (D-≈ (BS.complete {ℰʷ w} {ℰʷ v} same)) (back v))
    where
    same : proj₁ BS.⟦ ℰʷ w ⟧ ≡ proj₁ BS.⟦ ℰʷ v ⟧
    same = Eq.trans (bridge₂ (ℰʷ w))
             (Eq.trans (QM.mat-≐ (ᵀ-cong (exact {w = Dʷ (ℰʷ w)} {Dʷ (ℰʷ v)}
                                            (through (back w) (back v) e))))
                       (Eq.sym (bridge₂ (ℰʷ v))))

------------------------------------------------------------------------
-- One wire

module One where

  private
    variable
      w v : Word (TL.Gen 2)

    lt-irr : {a : Fin 2} → a Fin.< a → ⊥
    lt-irr {zero}     ()
    lt-irr {suc zero} (s≤s ())

    no1 : {a : Fin 2} → Fin.suc (Fin.zero {0}) Fin.< a → ⊥
    no1 {zero}     ()
    no1 {suc zero} (s≤s ())

    -- Three increasing indices, or two indices apart from a third.
    chain : {j k l : Fin 2} → j Fin.< k → k Fin.< l → ⊥
    chain {k = zero}     ()
    chain {k = suc zero} _ q = no1 q

    apart : (j k l : Fin 2) → .(k Fin.< l) → j ≢ k → j ≢ l → ⊥
    apart zero       zero       _          _ jk _  = jk refl
    apart (suc zero) (suc zero) _          _ jk _  = jk refl
    apart zero       (suc zero) zero       _ _  jl = jl refl
    apart zero       (suc zero) (suc zero) p _  _  = Irr.⊥-elim (lt-irr p)
    apart (suc zero) zero       (suc zero) _ _  jl = jl refl
    apart (suc zero) zero       zero       p _  _  = Irr.⊥-elim (lt-irr p)

    apart4 : (j k l m : Fin 2) → .(j Fin.< k) → .(l Fin.< m) → j ≢ l → ⊥
    apart4 zero       _ zero       _ _ _ jl = jl refl
    apart4 zero       _ (suc zero) _ _ q _  = Irr.⊥-elim (no1 q)
    apart4 (suc zero) _ _          _ p _ _  = Irr.⊥-elim (no1 p)

  -- Lemma 20: Greylyn's relations at n = 2, decoded, are derivable; the
  -- instances that need three or four distinct indices do not exist.
  D-rel : TL._===_ {2} w v → 1 ⊢ Dʷ₁ w ≈ Dʷ₁ v
  D-rel (TL.order-ω {j = zero})       = via Gorderω₀⁼ refl refl
  D-rel (TL.order-ω {j = suc zero})   = via Gorderω₁⁼ refl refl
  D-rel (TL.order-H _)                = via GorderH⁼ refl refl
  D-rel (TL.order-X _)                = via GorderX⁼ refl refl
  D-rel (TL.comm-ωω {j = zero} {k = zero} ne)           = ⊥-elim (ne refl)
  D-rel (TL.comm-ωω {j = zero} {k = suc zero} _)        = via Gcommωω₀₁⁼ refl refl
  D-rel (TL.comm-ωω {j = suc zero} {k = zero} _)        = via Gcommωω₁₀⁼ refl refl
  D-rel (TL.comm-ωω {j = suc zero} {k = suc zero} ne)   = ⊥-elim (ne refl)
  D-rel (TL.comm-ωH p jk jl)    = ⊥-elim (apart _ _ _ p jk jl)
  D-rel (TL.comm-ωX p jk jl)    = ⊥-elim (apart _ _ _ p jk jl)
  D-rel (TL.comm-HH p q jl _ _ _) = ⊥-elim (apart4 _ _ _ _ p q jl)
  D-rel (TL.comm-HX p q jl _ _ _) = ⊥-elim (apart4 _ _ _ _ p q jl)
  D-rel (TL.comm-XX p q jl _ _ _) = ⊥-elim (apart4 _ _ _ _ p q jl)
  D-rel (TL.swap-XX p q)    = Irr.⊥-elim (chain p q)
  D-rel (TL.swap-XX′ p q)   = Irr.⊥-elim (chain p q)
  D-rel (TL.swap-XH p q)    = Irr.⊥-elim (chain p q)
  D-rel (TL.swap-XH′ p q)   = Irr.⊥-elim (chain p q)
  D-rel (TL.rel-20 jk kl _) = Irr.⊥-elim (chain jk kl)
  D-rel (TL.swap-Xω {j = zero} {k = zero} p)           = Irr.⊥-elim (lt-irr p)
  D-rel (TL.swap-Xω {j = zero} {k = suc zero} _)       = via GswapXω⁼ refl refl
  D-rel (TL.swap-Xω {j = suc zero} {k = zero} p)       = Irr.⊥-elim (no1 p)
  D-rel (TL.swap-Xω {j = suc zero} {k = suc zero} p)   = Irr.⊥-elim (lt-irr p)
  D-rel (TL.swap-Xω′ {j = zero} {k = zero} p)           = Irr.⊥-elim (lt-irr p)
  D-rel (TL.swap-Xω′ {j = zero} {k = suc zero} _)       = via GswapXωp⁼ refl refl
  D-rel (TL.swap-Xω′ {j = suc zero} {k = zero} p)       = Irr.⊥-elim (no1 p)
  D-rel (TL.swap-Xω′ {j = suc zero} {k = suc zero} p)   = Irr.⊥-elim (lt-irr p)
  D-rel (TL.scalar-X {j = zero} {k = zero} p)           = Irr.⊥-elim (lt-irr p)
  D-rel (TL.scalar-X {j = zero} {k = suc zero} _)       = via GscalarX⁼ refl refl
  D-rel (TL.scalar-X {j = suc zero} {k = zero} p)       = Irr.⊥-elim (no1 p)
  D-rel (TL.scalar-X {j = suc zero} {k = suc zero} p)   = Irr.⊥-elim (lt-irr p)
  D-rel (TL.scalar-H {j = zero} {k = zero} p)           = Irr.⊥-elim (lt-irr p)
  D-rel (TL.scalar-H {j = zero} {k = suc zero} _)       = via GscalarH⁼ refl refl
  D-rel (TL.scalar-H {j = suc zero} {k = zero} p)       = Irr.⊥-elim (no1 p)
  D-rel (TL.scalar-H {j = suc zero} {k = suc zero} p)   = Irr.⊥-elim (lt-irr p)
  D-rel (TL.rel-18 {j = zero} {k = zero} p)           = Irr.⊥-elim (lt-irr p)
  D-rel (TL.rel-18 {j = zero} {k = suc zero} _)       = via Grel18⁼ refl refl
  D-rel (TL.rel-18 {j = suc zero} {k = zero} p)       = Irr.⊥-elim (no1 p)
  D-rel (TL.rel-18 {j = suc zero} {k = suc zero} p)   = Irr.⊥-elim (lt-irr p)
  D-rel (TL.rel-19 {j = zero} {k = zero} p)           = Irr.⊥-elim (lt-irr p)
  D-rel (TL.rel-19 {j = zero} {k = suc zero} _)       = via Grel19⁼ refl refl
  D-rel (TL.rel-19 {j = suc zero} {k = zero} p)       = Irr.⊥-elim (no1 p)
  D-rel (TL.rel-19 {j = suc zero} {k = suc zero} p)   = Irr.⊥-elim (lt-irr p)

  D-≈ : PB._≈_ (TL._===_ {2}) w v → 1 ⊢ Dʷ₁ w ≈ Dʷ₁ v
  D-≈ PB.refl        = PB.refl
  D-≈ (PB.sym e)     = PB.sym (D-≈ e)
  D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
  D-≈ (PB.cong e f)  = PB.cong (D-≈ e) (D-≈ f)
  D-≈ PB.assoc       = PB.assoc
  D-≈ PB.left-unit   = PB.left-unit
  D-≈ PB.right-unit  = PB.right-unit
  D-≈ (PB.axiom a)   = D-rel a

  -- Lemma 19.
  back-gen : (g : Gen 1) → 1 ⊢ Dʷ₁ (ℰ₁ g) ≈ [ g ]ʷ
  back-gen (gate₀ ⌈ ω-gate ⌉)   = via Gω⁼ refl refl
  back-gen (gate₁ ⌈ H-gate ⌉)   = PB.refl
  back-gen (gate₁ ⌈ T-gate ⌉)   = PB.refl
  back-gen (gate₀ ⌈ ω-gate ⌉ ↥) =
    PB.trans (via Gω⁼ refl refl) (PB.sym (PB.axiom (ω↑=ω ⌈ ω-gate ⌉)))

  back : (w : Circuit 1) → 1 ⊢ Dʷ₁ (ℰ₁ʷ w) ≈ w
  back [ g ]ʷ  = back-gen g
  back ε       = PB.refl
  back (w • v) = PB.cong (back w) (back v)

  complete : {w v : Circuit 1} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 1 ⊢ w ≈ v
  complete {w} {v} e =
    PB.trans (PB.sym (back w))
      (PB.trans (D-≈ (relations-complete (s≤s (s≤s z≤n)) {ℰ₁ʷ w} {ℰ₁ʷ v} same)) (back v))
    where
    same : TLS.⟦ ℰ₁ʷ w ⟧ᵐ ≡ TLS.⟦ ℰ₁ʷ v ⟧ᵐ
    same = Eq.trans (bridge₁ (ℰ₁ʷ w))
             (Eq.trans (QM.mat-≐ (ᵀ-cong (exact {w = Dʷ₁ (ℰ₁ʷ w)} {Dʷ₁ (ℰ₁ʷ v)}
                                            (through (back w) (back v) e))))
                       (Eq.sym (bridge₁ (ℰ₁ʷ v))))

------------------------------------------------------------------------
-- No wires: a power of ω

module Zero where

  ωs : ℕ → Circuit 0
  ωs zero    = ε
  ωs (suc k) = ω • ωs k

  count : Circuit 0 → ℕ
  count [ _ ]ʷ  = 1
  count ε       = 0
  count (w • v) = count w + count v

  private
    ωs-+ : (a b : ℕ) → 0 ⊢ ωs (a + b) ≈ ωs a • ωs b
    ωs-+ zero    b = PB.sym PB.left-unit
    ωs-+ (suc a) b = PB.trans (PB.cong PB.refl (ωs-+ a b)) (PB.sym PB.assoc)

    ωs-8 : 0 ⊢ ωs 8 ≈ ε
    ωs-8 = via ω⁸⁼ refl refl

    drop8 : (r q : ℕ) → 0 ⊢ ωs (r + q * 8) ≈ ωs r
    drop8 r zero    = Eq.subst (λ k → 0 ⊢ ωs k ≈ ωs r) (Eq.sym (ℕP.+-identityʳ r)) PB.refl
    drop8 r (suc q) =
      PB.trans (ωs-+ r (8 + q * 8))
      (PB.trans (PB.cong PB.refl (PB.trans (ωs-+ 8 (q * 8))
                                  (PB.trans (PB.cong ωs-8 PB.refl) PB.left-unit)))
      (PB.trans (PB.sym (ωs-+ r (q * 8))) (drop8 r q)))

  -- Every circuit on no wires is ω to the number of its gates, mod 8.
  nf : (w : Circuit 0) → 0 ⊢ w ≈ ωs (count w % 8)
  nf w = PB.trans (go w) (Eq.subst (λ k → 0 ⊢ ωs k ≈ ωs (count w % 8))
                             (Eq.sym (m≡m%n+[m/n]*n (count w) 8))
                             (drop8 (count w % 8) (count w / 8)))
    where
    go : (w : Circuit 0) → 0 ⊢ w ≈ ωs (count w)
    go [ gate₀ ⌈ ω-gate ⌉ ]ʷ = PB.sym PB.right-unit
    go ε       = PB.refl
    go (w • v) = PB.trans (PB.cong (go w) (go v)) (PB.sym (ωs-+ (count w) (count v)))

  -- The eight powers have different matrices: an exact equality is one\n  -- with no phase, which the matrices' entries refute.
  sep : (a b : ℕ) → a < 8 → b < 8 → Sem.⟦ ωs a ⟧ Sem.≈ Sem.⟦ ωs b ⟧ → a ≡ b
  sep 0 0 _ _ _ = refl
  sep 0 1 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 0 ⟧ Sem.⟦ ωs 1 ⟧ e)
  sep 0 2 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 0 ⟧ Sem.⟦ ωs 2 ⟧ e)
  sep 0 3 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 0 ⟧ Sem.⟦ ωs 3 ⟧ e)
  sep 0 4 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 0 ⟧ Sem.⟦ ωs 4 ⟧ e)
  sep 0 5 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 0 ⟧ Sem.⟦ ωs 5 ⟧ e)
  sep 0 6 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 0 ⟧ Sem.⟦ ωs 6 ⟧ e)
  sep 0 7 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 0 ⟧ Sem.⟦ ωs 7 ⟧ e)
  sep 1 0 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 1 ⟧ Sem.⟦ ωs 0 ⟧ e)
  sep 1 1 _ _ _ = refl
  sep 1 2 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 1 ⟧ Sem.⟦ ωs 2 ⟧ e)
  sep 1 3 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 1 ⟧ Sem.⟦ ωs 3 ⟧ e)
  sep 1 4 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 1 ⟧ Sem.⟦ ωs 4 ⟧ e)
  sep 1 5 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 1 ⟧ Sem.⟦ ωs 5 ⟧ e)
  sep 1 6 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 1 ⟧ Sem.⟦ ωs 6 ⟧ e)
  sep 1 7 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 1 ⟧ Sem.⟦ ωs 7 ⟧ e)
  sep 2 0 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 2 ⟧ Sem.⟦ ωs 0 ⟧ e)
  sep 2 1 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 2 ⟧ Sem.⟦ ωs 1 ⟧ e)
  sep 2 2 _ _ _ = refl
  sep 2 3 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 2 ⟧ Sem.⟦ ωs 3 ⟧ e)
  sep 2 4 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 2 ⟧ Sem.⟦ ωs 4 ⟧ e)
  sep 2 5 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 2 ⟧ Sem.⟦ ωs 5 ⟧ e)
  sep 2 6 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 2 ⟧ Sem.⟦ ωs 6 ⟧ e)
  sep 2 7 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 2 ⟧ Sem.⟦ ωs 7 ⟧ e)
  sep 3 0 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 3 ⟧ Sem.⟦ ωs 0 ⟧ e)
  sep 3 1 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 3 ⟧ Sem.⟦ ωs 1 ⟧ e)
  sep 3 2 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 3 ⟧ Sem.⟦ ωs 2 ⟧ e)
  sep 3 3 _ _ _ = refl
  sep 3 4 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 3 ⟧ Sem.⟦ ωs 4 ⟧ e)
  sep 3 5 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 3 ⟧ Sem.⟦ ωs 5 ⟧ e)
  sep 3 6 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 3 ⟧ Sem.⟦ ωs 6 ⟧ e)
  sep 3 7 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 3 ⟧ Sem.⟦ ωs 7 ⟧ e)
  sep 4 0 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 4 ⟧ Sem.⟦ ωs 0 ⟧ e)
  sep 4 1 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 4 ⟧ Sem.⟦ ωs 1 ⟧ e)
  sep 4 2 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 4 ⟧ Sem.⟦ ωs 2 ⟧ e)
  sep 4 3 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 4 ⟧ Sem.⟦ ωs 3 ⟧ e)
  sep 4 4 _ _ _ = refl
  sep 4 5 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 4 ⟧ Sem.⟦ ωs 5 ⟧ e)
  sep 4 6 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 4 ⟧ Sem.⟦ ωs 6 ⟧ e)
  sep 4 7 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 4 ⟧ Sem.⟦ ωs 7 ⟧ e)
  sep 5 0 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 5 ⟧ Sem.⟦ ωs 0 ⟧ e)
  sep 5 1 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 5 ⟧ Sem.⟦ ωs 1 ⟧ e)
  sep 5 2 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 5 ⟧ Sem.⟦ ωs 2 ⟧ e)
  sep 5 3 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 5 ⟧ Sem.⟦ ωs 3 ⟧ e)
  sep 5 4 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 5 ⟧ Sem.⟦ ωs 4 ⟧ e)
  sep 5 5 _ _ _ = refl
  sep 5 6 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 5 ⟧ Sem.⟦ ωs 6 ⟧ e)
  sep 5 7 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 5 ⟧ Sem.⟦ ωs 7 ⟧ e)
  sep 6 0 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 6 ⟧ Sem.⟦ ωs 0 ⟧ e)
  sep 6 1 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 6 ⟧ Sem.⟦ ωs 1 ⟧ e)
  sep 6 2 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 6 ⟧ Sem.⟦ ωs 2 ⟧ e)
  sep 6 3 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 6 ⟧ Sem.⟦ ωs 3 ⟧ e)
  sep 6 4 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 6 ⟧ Sem.⟦ ωs 4 ⟧ e)
  sep 6 5 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 6 ⟧ Sem.⟦ ωs 5 ⟧ e)
  sep 6 6 _ _ _ = refl
  sep 6 7 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 6 ⟧ Sem.⟦ ωs 7 ⟧ e)
  sep 7 0 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 7 ⟧ Sem.⟦ ωs 0 ⟧ e)
  sep 7 1 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 7 ⟧ Sem.⟦ ωs 1 ⟧ e)
  sep 7 2 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 7 ⟧ Sem.⟦ ωs 2 ⟧ e)
  sep 7 3 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 7 ⟧ Sem.⟦ ωs 3 ⟧ e)
  sep 7 4 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 7 ⟧ Sem.⟦ ωs 4 ⟧ e)
  sep 7 5 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 7 ⟧ Sem.⟦ ωs 5 ⟧ e)
  sep 7 6 _ _ (Exact.phased _ refl e) = ⊥-elim (O.eqₖ-complete 0 Sem.⟦ ωs 7 ⟧ Sem.⟦ ωs 6 ⟧ e)
  sep 7 7 _ _ _ = refl
  sep (suc (suc (suc (suc (suc (suc (suc (suc _)))))))) _ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) _ _
  sep _ (suc (suc (suc (suc (suc (suc (suc (suc _)))))))) _ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) _

  complete : {w v : Circuit 0} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 0 ⊢ w ≈ v
  complete {w} {v} e =
    PB.trans (nf w)
      (PB.trans (Eq.subst (λ k → 0 ⊢ ωs (count w % 8) ≈ ωs k)
                  (sep (count w % 8) (count v % 8) (m%n<n (count w) 8) (m%n<n (count v) 8)
                       (through (PB.sym (nf w)) (PB.sym (nf v)) e))
                  PB.refl)
                (PB.sym (nf v)))

------------------------------------------------------------------------
-- Completeness up to two qubits

complete : n ≤ 2 → {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
complete {zero}                z≤n             = Zero.complete
complete {suc zero}            (s≤s z≤n)       = One.complete
complete {suc (suc zero)}      (s≤s (s≤s z≤n)) = Two.complete
complete {suc (suc (suc n))}   (s≤s (s≤s ()))

-- So the rule set presents the semantics on up to two wires.
sound-complete : n ≤ 2 → {w v : Circuit n} → (n ⊢ w ≈ v) ⇔ (Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧)
sound-complete le = mk⇔ Sem.sound (complete le)
