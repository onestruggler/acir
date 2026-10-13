"""Write Examples/Independence/Clifford+CS/Completeness.agda: CliffCS₂
complete on zero, one and three wires, Lemma 20's clauses taken from
cs3.py's relations (their names are the source's constructors)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cs3 import R

drel = '\n'.join('  D-rel CS.%s = via D%s⁼ refl refl' % (k, k[3:]) for k in R)

text = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂ is complete for the matrix semantics on zero, one and
-- three wires (Theorem 22(5), by transfer)
--
-- Section 4 of Blake's paper.  On three wires, from Bian and Selinger's
-- presentation of 3-qubit Clifford+CS operators (Examples.Groups.
-- Clifford+CS-3qubit), complete for its 8 × 8 matrices over 𝔻[i]; on
-- at most one wire, from Cliff₂'s completeness (Clifford+CS.Low).  Two
-- wires are not covered: the 3-qubit theorem says nothing of 2-qubit
-- circuits, and no presentation of 2-qubit Clifford+CS operators is
-- formalised here.
--
-- The encoding ℰʷ (Clifford+CS.Bridge) drops ω and turns H into
-- K = ω† H, since ω is not in 𝔻[i]; the decoding Dʷ sends their words
-- back letter for letter, K as ω⁷ H and i as ω².  So decoding the
-- encoding gives the circuit back after the c w powers of ω it lost
-- (Lemma 19: back), and every relation of theirs decodes to a
-- derivation of CliffCS₂'s (Lemma 20: Clifford+CS.Decodings, the
-- paper's Appendix G.5 over its Appendix E).  Two circuits w, v with
-- equal matrices then give ω^(7 c w) w ≈ Dʷ (ℰʷ w) and
-- ω^(7 c w) v ≈ ω^t Dʷ (ℰʷ v), t = 7 c w + c v, whose readings agree.
-- If t is odd, that says ω times ι of a unitary matrix over 𝔻[i] is ι
-- of another, which it is not (Bridge.no-odd); so t = 2q, ω^t is the
-- decoding of i^q, their matrices of ℰʷ w and i^q ℰʷ v are equal
-- (Bridge.same), their rules derive the one from the other, CliffCS₂'s
-- derive the decodings, and ω^(7 c w) cancels.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Completeness where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _+_ ; _*_ ; s≤s ; z≤n ; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module CliffordCS)
import Examples.Groups.Clifford+CS-3qubit.Presentation as BS

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Sem
open import Examples.Independence.Clifford+CS.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf ; lift⁼ ; ω⁸⁼)
open import Examples.Independence.Clifford+CS.Decodings
open import Examples.Independence.Clifford+CS.Bridge
  using (ℰ ; ℰʷ ; Dʷ ; ωs ; SW01 ; SW12 ; ⟪ωs•⟫ ; exact ; same ; no-odd)
open import Examples.Independence.Semantics.Reading using (module QI) renaming (⟪_⟫ to ⟪_⟫ᴰ)
open import Examples.Independence.Clifford+CS.Low using (complete₀ ; complete₁)
import Examples.Independence.Reasoning Gate as R
open R.Theory arity lhs rhs using (lift)

open Central-Scalars (λ { ⌈ ω-gate ⌉ ⌈ ω-gate ⌉ → PB.refl }) using (comm-gate₀-w)

module CS = CliffordCS

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

------------------------------------------------------------------------
-- Powers of ω

private
  ωs-comm : (k : ℕ) (u : Circuit n) → n ⊢ ωs k • u ≈ u • ωs k
  ωs-comm zero    u = PB.trans PB.left-unit (PB.sym PB.right-unit)
  ωs-comm (suc k) u =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (ωs-comm k u))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (PB.sym (comm-gate₀-w ⌈ ω-gate ⌉ u)) PB.refl) PB.assoc)))

  ωs-+ : (a b : ℕ) → n ⊢ ωs (a + b) ≈ ωs a • ωs b
  ωs-+ zero    b = PB.sym PB.left-unit
  ωs-+ (suc a) b = PB.trans (PB.cong PB.refl (ωs-+ a b)) (PB.sym PB.assoc)

  ωs-8 : (m : ℕ) → n ⊢ ωs (8 * m) ≈ ε
  ωs-8 zero    = PB.refl
  ωs-8 {n} (suc m) =
    Eq.subst (λ k → n ⊢ ωs k ≈ ε) (Eq.sym (ℕP.*-suc 8 m))
      (PB.trans (ωs-+ 8 (8 * m)) (PB.trans (PB.cong (via ω⁸⁼ refl refl) (ωs-8 m)) PB.left-unit))

  -- ω^(7k) cancels: ω^k ω^(7k) = ω^(8k) = ε.
  unω : (k : ℕ) {x y : Circuit n} → n ⊢ ωs (7 * k) • x ≈ ωs (7 * k) • y → n ⊢ x ≈ y
  unω k {x} {y} e = PB.trans (pre x) (PB.trans (PB.cong PB.refl e) (PB.sym (pre y)))
    where
    pre : (z : Circuit _) → _ ⊢ z ≈ ωs k • (ωs (7 * k) • z)
    pre z = PB.trans (PB.sym PB.left-unit)
            (PB.trans (PB.cong (PB.trans (PB.sym (ωs-8 k)) (ωs-+ k (7 * k))) PB.refl) PB.assoc)

------------------------------------------------------------------------
-- Three wires

module Three where

  private
    variable
      w v : Word CS.Gen

  -- Lemma 20: their relations, decoded, are derivable.
  D-rel : CS.Rel w v → 3 ⊢ Dʷ w ≈ Dʷ v
%(drel)s

  -- So every derivation of theirs.
  D-≈ : PB._≈_ CS.Rel w v → 3 ⊢ Dʷ w ≈ Dʷ v
  D-≈ PB.refl        = PB.refl
  D-≈ (PB.sym e)     = PB.sym (D-≈ e)
  D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
  D-≈ (PB.cong e f)  = PB.cong (D-≈ e) (D-≈ f)
  D-≈ PB.assoc       = PB.assoc
  D-≈ PB.left-unit   = PB.left-unit
  D-≈ PB.right-unit  = PB.right-unit
  D-≈ (PB.axiom a)   = D-rel a

  -- What the encoding drops: one ω for each ω and each H.
  c₀ : Gen 3 → ℕ
  c₀ (gate₀ ⌈ ω-gate ⌉)           = 1
  c₀ (gate₁ ⌈ H-gate ⌉)           = 1
  c₀ (gate₀ ⌈ ω-gate ⌉ ↥)         = 1
  c₀ (gate₁ ⌈ H-gate ⌉ ↥)         = 1
  c₀ ((gate₀ ⌈ ω-gate ⌉ ↥) ↥)     = 1
  c₀ ((gate₁ ⌈ H-gate ⌉ ↥) ↥)     = 1
  c₀ (((gate₀ ⌈ ω-gate ⌉ ↥) ↥) ↥) = 1
  c₀ _                            = 0

  c : Circuit 3 → ℕ
  c [ g ]ʷ  = c₀ g
  c ε       = 0
  c (w • v) = c w + c v

  -- Lemma 19: decoding the encoding.
  private
    ω↑ : 3 ⊢ ω ↑ ≈ ω
    ω↑ = PB.axiom (ω↑=ω ⌈ ω-gate ⌉)

    ω↑↑ : 3 ⊢ ω ↑ ↑ ≈ ω
    ω↑↑ = PB.trans (lift (PB.axiom (ω↑=ω ⌈ ω-gate ⌉))) ω↑

    ω↑↑↑ : 3 ⊢ ω ↑ ↑ ↑ ≈ ω
    ω↑↑↑ = PB.trans (lift (PB.trans (lift (PB.axiom (ω↑=ω ⌈ ω-gate ⌉)))
                                   (PB.axiom (ω↑=ω ⌈ ω-gate ⌉)))) ω↑

    ω-ε : 3 ⊢ ωs 1 • Dʷ ε ≈ ω
    ω-ε = PP.by-assoc (3 VRel,_===_) refl

    plain : {u v : Circuit 3} → Assoc.to-list (3 VRel,_===_) u ≡ Assoc.to-list (3 VRel,_===_) v →
            3 ⊢ u ≈ v
    plain = PP.by-assoc (3 VRel,_===_)

  back-gen : (g : Gen 3) → 3 ⊢ ωs (c₀ g) • Dʷ (ℰ g) ≈ [ g ]ʷ
  back-gen (gate₀ ⌈ ω-gate ⌉)           = ω-ε
  back-gen (gate₁ ⌈ H-gate ⌉)           = via L19H⁼ refl refl
  back-gen (gate₁ ⌈ S-gate ⌉)           = plain refl
  back-gen (gate₂ ⌈ CS-gate ⌉)          = plain refl
  back-gen (gate₂ swap)                 = via Dσ⁼ refl refl
  back-gen (gate₀ ⌈ ω-gate ⌉ ↥)         = PB.trans ω-ε (PB.sym ω↑)
  back-gen (gate₁ ⌈ H-gate ⌉ ↥)         = via (lift⁼ L19H⁼) refl refl
  back-gen (gate₁ ⌈ S-gate ⌉ ↥)         = plain refl
  back-gen (gate₂ ⌈ CS-gate ⌉ ↥)        = plain refl
  back-gen (gate₂ swap ↥)               = via (lift⁼ Dσ⁼) refl refl
  back-gen ((gate₀ ⌈ ω-gate ⌉ ↥) ↥)     = PB.trans ω-ε (PB.sym ω↑↑)
  back-gen ((gate₁ ⌈ H-gate ⌉ ↥) ↥)     = via (lift⁼ (lift⁼ L19H⁼)) refl refl
  back-gen ((gate₁ ⌈ S-gate ⌉ ↥) ↥)     = plain refl
  back-gen (((gate₀ ⌈ ω-gate ⌉ ↥) ↥) ↥) = PB.trans ω-ε (PB.sym ω↑↑↑)

  back : (w : Circuit 3) → 3 ⊢ ωs (c w) • Dʷ (ℰʷ w) ≈ w
  back [ g ]ʷ  = back-gen g
  back ε       = PB.left-unit
  back (w • v) =
    PB.trans (PB.cong (ωs-+ (c w) (c v)) PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
                (PB.trans (PB.cong (ωs-comm (c v) (Dʷ (ℰʷ w))) PB.refl) PB.assoc)))
    (PB.trans (PB.sym PB.assoc) (PB.cong (back w) (back v)))))

  -- i^q, and its decoding ω^(2q).
  iIs : ℕ → Word CS.Gen
  iIs zero    = ε
  iIs (suc q) = CS.iI • iIs q

  ωs-iIs : (q : ℕ) → 3 ⊢ ωs (q * 2) ≈ Dʷ (iIs q)
  ωs-iIs zero    = PB.refl
  ωs-iIs (suc q) =
    PB.trans (PB.sym PB.assoc) (PB.cong (plain refl) (ωs-iIs q))

  -- Parity.
  data Par : ℕ → Set where
    even : (q : ℕ) → Par (q * 2)
    odd  : (q : ℕ) → Par (suc (q * 2))

  par : (t : ℕ) → Par t
  par zero          = even 0
  par (suc zero)    = odd 0
  par (suc (suc t)) with par t
  ... | even q = even (suc q)
  ... | odd q  = odd (suc q)

  private
    Rd : Circuit 3 → QI.Op 3
    Rd x = ⟪ Sem.⟦ x ⟧ ⟫ᴰ

    readings : {x y : Circuit 3} → 3 ⊢ x ≈ y → Rd x QI.≐ Rd y
    readings {x} {y} d = exact {w = x} {y} (Sem.sound d)

    -- The end of the argument, at any t: even, the decodings' words are
    -- equal by their rules; odd, impossible.
    finish : (k : ℕ) {w v : Circuit 3} (a b : Word CS.Gen) (t : ℕ) → Par t →
             3 ⊢ ωs (7 * k) • w ≈ Dʷ a → 3 ⊢ ωs (7 * k) • v ≈ ωs t • Dʷ b →
             Rd (Dʷ a) QI.≐ Rd (ωs t • Dʷ b) → 3 ⊢ w ≈ v
    finish k a b .(q * 2) (even q) s₁ s₂ r =
      unω k (PB.trans s₁ (PB.trans (D-≈ (BS.complete {a} {iIs q • b} (same a (iIs q • b) r′)))
                                   (PB.trans (PB.cong (PB.sym (ωs-iIs q)) PB.refl) (PB.sym s₂))))
      where
      r′ : Rd (Dʷ a) QI.≐ Rd (Dʷ (iIs q • b))
      r′ = QI.≐-trans r (readings (PB.cong (ωs-iIs q) PB.refl))
    finish k a b .(suc (q * 2)) (odd q) s₁ s₂ r =
      ⊥-elim (no-odd a (iIs q • b) (QI.≐-trans r (readings (PB.trans PB.assoc
                (PB.cong PB.refl (PB.cong (ωs-iIs q) PB.refl))))))

  complete : {w v : Circuit 3} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 3 ⊢ w ≈ v
  complete {w} {v} e = finish (c w) a b t (par t) s₁ s₂ r
    where
    a = ℰʷ w
    b = ℰʷ v
    t = 7 * c w + c v

    s₁ : 3 ⊢ ωs (7 * c w) • w ≈ Dʷ a
    s₁ = PB.trans (PB.cong PB.refl (PB.sym (back w)))
         (PB.trans (PB.sym PB.assoc)
         (PB.trans (PB.cong (PB.trans (ωs-comm (7 * c w) (ωs (c w)))
                              (PB.trans (PB.sym (ωs-+ (c w) (7 * c w))) (ωs-8 (c w))))
                            PB.refl)
                   PB.left-unit))

    s₂ : 3 ⊢ ωs (7 * c w) • v ≈ ωs t • Dʷ b
    s₂ = PB.trans (PB.cong PB.refl (PB.sym (back v)))
         (PB.trans (PB.sym PB.assoc) (PB.cong (PB.sym (ωs-+ (7 * c w) (c v))) PB.refl))

    r : Rd (Dʷ a) QI.≐ Rd (ωs t • Dʷ b)
    r = QI.≐-trans (QI.≐-sym (readings s₁))
        (QI.≐-trans (⟪ωs•⟫ (7 * c w) w)
        (QI.≐-trans (QI.scale-cong (exact {w = w} {v} e))
        (QI.≐-trans (QI.≐-sym (⟪ωs•⟫ (7 * c w) v)) (readings s₂))))

------------------------------------------------------------------------
-- Completeness on zero, one and three wires

complete : n ≤ 1 ⊎ n ≡ 3 → {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
complete (inj₁ z≤n)       = complete₀
complete (inj₁ (s≤s z≤n)) = complete₁
complete (inj₂ refl)      = Three.complete

-- So the rule set presents the semantics on those widths.
sound-complete : n ≤ 1 ⊎ n ≡ 3 → {w v : Circuit n} → (n ⊢ w ≈ v) ⇔ (Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧)
sound-complete le = mk⇔ Sem.sound (complete le)
'''

out = text.replace('%(drel)s', drel)
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'Clifford+CS', 'Completeness.agda')
open(path, 'w', encoding='utf-8').write(out)
print('ok')
