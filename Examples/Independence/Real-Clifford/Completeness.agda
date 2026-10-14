------------------------------------------------------------------------
-- Presentations of groups
--
-- RCliff₂ is complete for the matrix semantics (Theorem 22(2), by
-- transfer)
--
-- Section 4 of Blake's paper, from Makary, Ross and Selinger's
-- presentation of the real Clifford group (Examples.Groups.Real-
-- Clifford, complete over 𝔻[ω]).  The encoding ℰ (Real-Clifford.Bridge)
-- sends a circuit to their words, and their matrix of the encoding is
-- RCliff₂'s (bridge, exact), so two circuits with equal matrices have
-- equal encodings by their rules.  The decoding Dʷ sends their words
-- back, reading them backwards and CZ as H CNOT H on the target; every
-- one of R1–R16 decodes to a derivation of RCliff₂'s (Lemma 20:
-- Real-Clifford.Derivations), so equal encodings have equal decodings;
-- and decoding the encoding gives the circuit back (Lemma 19: back).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Real-Clifford.Completeness where

open import Data.Nat.Base using (ℕ)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₂₊)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring using (D ; RingD ; isCommutativeRing-D ; √½)
open import Examples.Groups.Real-Clifford.Presentation.DOmega using (√½-sq ; 1≢0)
import Examples.Groups.Real-Clifford.Syntactics as Q
import Examples.Groups.Real-Clifford.Semantics.Completeness as QComplete

open import Examples.Independence.Real-Clifford.Syntactics
import Examples.Independence.Real-Clifford.Semantics as Sem
open import Examples.Independence.Real-Clifford.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf)
open import Examples.Independence.Real-Clifford.Derivations
open import Examples.Independence.Real-Clifford.Bridge using (ℰ ; ℰʷ ; bridge ; exact ; module RL)
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (lift)

module QC = QComplete {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq 1≢0

private
  variable
    n : ℕ
    w v : Q.Circuit n

------------------------------------------------------------------------
-- The decoding

D₀ : Q.Gen n → Circuit n
D₀ (Q.gate₀ Q.neg-gate) = neg
D₀ (Q.gate₁ Q.H-gate)   = H
D₀ (Q.gate₁ Q.Z-gate)   = Z
D₀ (Q.gate₂ Q.CZ-gate)  = H • CX • H
D₀ (g Q.↥)              = D₀ g ↑

-- A word of theirs, read backwards.
Dʷ : Q.Circuit n → Circuit n
Dʷ [ g ]ʷ  = D₀ g
Dʷ ε       = ε
Dʷ (w • v) = Dʷ v • Dʷ w

D-↑ : (w : Q.Circuit n) → Dʷ (w Q.↑) ≡ Dʷ w ↑
D-↑ [ g ]ʷ  = refl
D-↑ ε       = refl
D-↑ (w • v) = Eq.cong₂ _•_ (D-↑ v) (D-↑ w)

------------------------------------------------------------------------
-- Lemma 20: their rules, decoded, are derivable

private
  -- An equation of letter lists, read between words.
  via : {w v : Circuit n} (e : Eqn n) →
        Assoc.to-list (n VRel,_===_) w ≡ Assoc.to-list (n VRel,_===_) ⟪ lhs⁼ e ⟫ →
        Assoc.to-list (n VRel,_===_) ⟪ rhs⁼ e ⟫ ≡ Assoc.to-list (n VRel,_===_) v →
        n ⊢ w ≈ v
  via {n} e p q =
    PB.trans (PP.by-assoc (n VRel,_===_) p) (PB.trans (prf e) (PP.by-assoc (n VRel,_===_) q))

D-rel : n Q.SRel, w === v → n ⊢ Dʷ w ≈ Dʷ v
D-rel Q.R₁  = via DR₁⁼ refl refl
D-rel Q.R₂  = via DR₂⁼ refl refl
D-rel Q.R₃  = via DR₃⁼ refl refl
D-rel Q.R₄  = via DR₄⁼ refl refl
D-rel Q.R₅  = via DR₅⁼ refl refl
D-rel Q.R₆  = via DR₆⁼ refl refl
D-rel Q.R₇  = via DR₇⁼ refl refl
D-rel Q.R₈  = via DR₈⁼ refl refl
D-rel Q.R₉  = via DR₉⁼ refl refl
D-rel Q.R₁₀ = via DR₁₀⁼ refl refl
D-rel Q.R₁₁ = via DR₁₁⁼ refl refl
D-rel Q.R₁₂ = via DR₁₂⁼ refl refl
D-rel Q.R₁₃ = via DR₁₃⁼ refl refl
D-rel Q.R₁₄ = via DR₁₄⁼ refl refl
D-rel Q.R₁₅ = via DR₁₅⁼ refl refl
D-rel Q.R₁₆ = via DR₁₆⁼ refl refl

private
  -- The decoded CZ passes anything two wires up.
  pass-CZ : (W : Circuit n) → (₂₊ n) ⊢ (H • CX • H) • W ↑ ↑ ≈ W ↑ ↑ • (H • CX • H)
  pass-CZ {n} W = begin
    (H • CX • H) • W′            ≈⟨ assoc ⟩
    H • (CX • H) • W′            ≈⟨ cong refl assoc ⟩
    H • CX • H • W′              ≈⟨ cong refl (cong refl (sym cH)) ⟩
    H • CX • W′ • H              ≈⟨ cong refl (sym assoc) ⟩
    H • (CX • W′) • H            ≈⟨ cong refl (cong (sym cX) refl) ⟩
    H • (W′ • CX) • H            ≈⟨ cong refl assoc ⟩
    H • W′ • CX • H              ≈⟨ sym assoc ⟩
    (H • W′) • CX • H            ≈⟨ cong (sym cH) refl ⟩
    (W′ • H) • CX • H            ≈⟨ assoc ⟩
    W′ • H • CX • H              ∎
    where
    open PB ((₂₊ n) VRel,_===_)
    open PP ((₂₊ n) VRel,_===_) using (word-setoid)
    open import Relation.Binary.Reasoning.Setoid word-setoid
    W′ = W ↑ ↑
    cH : W′ • H ≈ H • W′
    cH = comm-gate₁-w↑ ⌈ H-gate ⌉ (W ↑)
    cX : W′ • CX ≈ CX • W′
    cX = comm-gate₂-w↑↑ ⌈ CX-gate ⌉ W

-- With the structural rules.
D-ax : n Q.VRel, w === v → n ⊢ Dʷ w ≈ Dʷ v
D-ax (Q.srel r)                 = D-rel r
D-ax (Q.cong↑ {w = w} {v} r)    =
  Eq.subst₂ (_ ⊢_≈_) (Eq.sym (D-↑ w)) (Eq.sym (D-↑ v)) (lift (D-ax r))
D-ax (Q.comm₁ Q.H-gate g)       = PB.sym (comm-gate₁-w↑ ⌈ H-gate ⌉ (D₀ g))
D-ax (Q.comm₁ Q.Z-gate g)       = PB.sym (comm-gate₁-w↑ ⌈ Z-gate ⌉ (D₀ g))
D-ax (Q.comm₂ Q.CZ-gate g)      = pass-CZ (D₀ g)
D-ax (Q.ω↑=ω Q.neg-gate)        = PB.axiom (ω↑=ω ⌈ m-gate ⌉)

-- So every derivation of theirs.
D-≈ : n Q.⊢ w ≈ v → n ⊢ Dʷ w ≈ Dʷ v
D-≈ PB.refl        = PB.refl
D-≈ (PB.sym e)     = PB.sym (D-≈ e)
D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
D-≈ (PB.cong e f)  = PB.cong (D-≈ f) (D-≈ e)
D-≈ PB.assoc       = PB.sym PB.assoc
D-≈ PB.left-unit   = PB.right-unit
D-≈ PB.right-unit  = PB.left-unit
D-≈ (PB.axiom a)   = D-ax a

------------------------------------------------------------------------
-- Lemma 19: decoding the encoding

back-gen : (g : Gen n) → n ⊢ Dʷ (ℰ g) ≈ [ g ]ʷ
back-gen (gate₀ ⌈ m-gate ⌉)  = PB.refl
back-gen (gate₁ ⌈ H-gate ⌉)  = PB.refl
back-gen (gate₁ ⌈ Z-gate ⌉)  = PB.refl
back-gen (gate₂ ⌈ CX-gate ⌉) = via DCX⁼ refl refl
back-gen (gate₂ swap)        = via Dσ⁼ refl refl
back-gen (gate₃ ⌈ () ⌉)
back-gen (g ↥)               =
  Eq.subst (λ x → _ ⊢ x ≈ [ g ↥ ]ʷ) (Eq.sym (D-↑ (ℰ g))) (lift (back-gen g))

back : (w : Circuit n) → n ⊢ Dʷ (ℰʷ w) ≈ w
back [ g ]ʷ  = back-gen g
back ε       = PB.refl
back (w • v) = PB.cong (back w) (back v)

------------------------------------------------------------------------
-- Completeness

-- Circuits with the same matrix are equal by RCliff₂, at every width.
complete : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
complete {w = w} {v} e =
  PB.trans (PB.sym (back w))
    (PB.trans (D-≈ (QC.completeness {w = ℰʷ w} {v = ℰʷ v}
                     (RL.≐-trans (bridge w) (RL.≐-trans (exact {w = w} {v} e) (RL.≐-sym (bridge v))))))
              (back v))

-- So the rule set presents the semantics.
sound-complete : {w v : Circuit n} → (n ⊢ w ≈ v) ⇔ (Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧)
sound-complete = mk⇔ Sem.sound complete
