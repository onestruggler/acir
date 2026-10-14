------------------------------------------------------------------------
-- Presentations of groups
--
-- Cliff₃ is complete (Theorem 22(3)), by transfer from Paper-V0
--
-- Circuits with equal matrices have encodings equal by Paper-V0's rules
-- at p = 3 (Bridge).  Paper-V0's rules hold only up to scalars, which
-- it erased; decoded into Cliff₃ (Dʷ reads H and S as themselves and
-- CZ as H† CX H, and reverses a word, Paper-V0's words being in
-- operator order) each holds up to a power of ω (Derivations), and so
-- does every derivation (D-≈).  Every gate is a power of ω times the
-- decoding of its encoding (back), so circuits with equal matrices are
-- equal up to a power ωᵏ.  Then ωᵏ has the identity's matrix, so ζᵏ = 1,
-- 12 divides k, and ωᵏ is ε by (ω¹²).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Qutrit-Clifford.Completeness where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _%_ ; _/_ ; _<_ ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n ; m%n<n)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_ ; replicate)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Independence.Qutrit-Clifford.Syntactics
open import Examples.Independence.Qutrit-Clifford.Kit
  using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf ; sym⁼ ; ω¹²⁼ ; H⁴⁼ ; S³⁼ ; σσ⁼)
open import Examples.Independence.Qutrit-Clifford.Derivations
open import Examples.Independence.Qutrit-Clifford.Encoding using (E₀ ; E₀ʷ)
open import Examples.Independence.Qutrit-Clifford.Bridge using (bridge)
import Examples.Independence.Qutrit-Clifford.Semantics as Sem
open import Examples.Independence.Semantics.Qutrit
  using (εs ; x ; _^_ ; 1q ; Q ; R ; √3 ; ix ; δv ; δ₁ ; scal ; _⊙_ ; _≐_ ; Digits ;
         Σv ; Σ-cong ; Σ-scaleˡ ; Σ-δˡ ; ix-mul ; ix-scalM ; ix-id ; x^-mod ; module Circuits)
  renaming (_*_ to _*ᵠ_)
import Examples.Independence.Qutrit-Clifford.P3 as P3

import Examples.Groups.Symplectic.Syntactics.Gates 1 P3.p-prime as Gates
open Gates.Symplectic using ()
  renaming (Gen to VGen ; gate₁ to vg₁ ; gate₂ to vg₂ ; _↥ to _↥ᵛ ;
            H-gate to vH ; S-gate to vS ; CZ-gate to vCZ)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  P3.p-3 P3.p-prime P3.g* P3.g-gen as Pap
open Pap.Clifford-Relations using ()
  renaming (_QRel,_===_ to _V0,_===_ ; srel to srelᵛ ; cong↑ to cong↑ᵛ ;
            comm₁ to comm₁ᵛ ; comm₂ to comm₂ᵛ)
module VB = Pap.Clifford-Relations.Base

open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ)

private
  variable
    n : ℕ

  one : (h h' : PGate 0) → h ≡ h'
  one ⌈ ω-gate ⌉ ⌈ ω-gate ⌉ = refl

open Single-Scalar one using (comm-gate₀-w)

------------------------------------------------------------------------
-- Powers of ω

ωᵏ : ℕ → Circuit n
ωᵏ zero    = ε
ωᵏ (suc k) = ω • ωᵏ k

module Scalars {n : ℕ} where

  open PB (n VRel,_===_)
  open PP (n VRel,_===_) using (word-setoid)
  open import Relation.Binary.Reasoning.Setoid word-setoid

  -- ω commutes with every circuit, and so do its powers.
  ωᵏ-central : (k : ℕ) (w : Circuit n) → w • ωᵏ k ≈ ωᵏ k • w
  ωᵏ-central zero    w = trans right-unit (sym left-unit)
  ωᵏ-central (suc k) w = begin
    w • (ω • ωᵏ k)      ≈⟨ sym assoc ⟩
    (w • ω) • ωᵏ k      ≈⟨ cong (comm-gate₀-w ⌈ ω-gate ⌉ w) refl ⟩
    (ω • w) • ωᵏ k      ≈⟨ assoc ⟩
    ω • (w • ωᵏ k)      ≈⟨ cong refl (ωᵏ-central k w) ⟩
    ω • (ωᵏ k • w)      ≈⟨ sym assoc ⟩
    (ω • ωᵏ k) • w      ∎

  ωᵏ-+ : (a b : ℕ) → ωᵏ (a + b) ≈ ωᵏ a • ωᵏ b
  ωᵏ-+ zero    b = sym left-unit
  ωᵏ-+ (suc a) b = trans (cong refl (ωᵏ-+ a b)) (sym assoc)

  ωᵏ¹² : ωᵏ 12 ≈ ε
  ωᵏ¹² = trans (PP.by-assoc (n VRel,_===_) refl) (prf (ω¹²⁼ {n}))

  ωᵏ-12 : (y : ℕ) → ωᵏ (y * 12) ≈ ε
  ωᵏ-12 zero    = refl
  ωᵏ-12 (suc y) = trans (ωᵏ-+ 12 (y * 12)) (trans (cong ωᵏ¹² (ωᵏ-12 y)) left-unit)

  -- ωᵏ depends on k mod 12 only.
  ωᵏ-mod : (k : ℕ) → ωᵏ k ≈ ωᵏ (k % 12)
  ωᵏ-mod k = begin
    ωᵏ k                                 ≡⟨ Eq.cong ωᵏ (m≡m%n+[m/n]*n k 12) ⟩
    ωᵏ (k % 12 + (k / 12) * 12)          ≈⟨ ωᵏ-+ (k % 12) ((k / 12) * 12) ⟩
    ωᵏ (k % 12) • ωᵏ ((k / 12) * 12)     ≈⟨ cong refl (ωᵏ-12 (k / 12)) ⟩
    ωᵏ (k % 12) • ε                      ≈⟨ right-unit ⟩
    ωᵏ (k % 12)                          ∎

  -- ω^(11 c) inverts ω^c.
  ωᵏ-inv : (c : ℕ) → ωᵏ (c * 11) • ωᵏ c ≈ ε
  ωᵏ-inv c = begin
    ωᵏ (c * 11) • ωᵏ c     ≈⟨ sym (ωᵏ-+ (c * 11) c) ⟩
    ωᵏ (c * 11 + c)        ≡⟨ Eq.cong ωᵏ (Eq.trans (ℕP.+-comm (c * 11) c) (Eq.sym (ℕP.*-suc c 11))) ⟩
    ωᵏ (c * 12)            ≈⟨ ωᵏ-12 c ⟩
    ε                      ∎

  ω-shift : (a b : ℕ) (w : Circuit n) → ωᵏ a • (ωᵏ b • w) ≈ ωᵏ (a + b) • w
  ω-shift a b w = trans (sym assoc) (cong (sym (ωᵏ-+ a b)) refl)

  ω-pull : (a b : ℕ) (w v : Circuit n) → (ωᵏ a • w) • (ωᵏ b • v) ≈ ωᵏ (a + b) • (w • v)
  ω-pull a b w v = begin
    (ωᵏ a • w) • (ωᵏ b • v)      ≈⟨ assoc ⟩
    ωᵏ a • (w • (ωᵏ b • v))      ≈⟨ cong refl (sym assoc) ⟩
    ωᵏ a • ((w • ωᵏ b) • v)      ≈⟨ cong refl (cong (ωᵏ-central b w) refl) ⟩
    ωᵏ a • ((ωᵏ b • w) • v)      ≈⟨ cong refl assoc ⟩
    ωᵏ a • (ωᵏ b • (w • v))      ≈⟨ ω-shift a b (w • v) ⟩
    ωᵏ (a + b) • (w • v)         ∎

  -- An equation up to ω^c, read the other way.
  ω-flip : (c : ℕ) {w v : Circuit n} → w ≈ ωᵏ c • v → v ≈ ωᵏ (c * 11) • w
  ω-flip c {w} {v} e = begin
    v                              ≈⟨ sym left-unit ⟩
    ε • v                          ≈⟨ cong (sym (ωᵏ-inv c)) refl ⟩
    (ωᵏ (c * 11) • ωᵏ c) • v       ≈⟨ assoc ⟩
    ωᵏ (c * 11) • (ωᵏ c • v)       ≈⟨ cong refl (sym e) ⟩
    ωᵏ (c * 11) • w                ∎

open Scalars public

-- ω one wire up is ω.
ωᵏ-↑ : (k : ℕ) → (₁₊ n) ⊢ ωᵏ k ↑ ≈ ωᵏ k
ωᵏ-↑ zero    = PB.refl
ωᵏ-↑ (suc k) = PB.cong (PB.axiom (ω↑=ω ⌈ ω-gate ⌉)) (ωᵏ-↑ k)

-- An equation up to a power of ω.
infix 4 _⊢_≈ω_
_⊢_≈ω_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ω v = Σ ℕ λ c → n ⊢ w ≈ ωᵏ c • v

------------------------------------------------------------------------
-- Reading an equation of letter lists between words

private
  via : {w v : Circuit n} (e : Eqn n) →
        Assoc.to-list (n VRel,_===_) w ≡ Assoc.to-list (n VRel,_===_) ⟪ lhs⁼ e ⟫ →
        Assoc.to-list (n VRel,_===_) ⟪ rhs⁼ e ⟫ ≡ Assoc.to-list (n VRel,_===_) v →
        n ⊢ w ≈ v
  via {n} e p q =
    PB.trans (PP.by-assoc (n VRel,_===_) p) (PB.trans (prf e) (PP.by-assoc (n VRel,_===_) q))

------------------------------------------------------------------------
-- The decoding of a Paper-V0 word

d : VGen n → Circuit n
d (vg₁ vH)  = H
d (vg₁ vS)  = S
d (vg₂ vCZ) = H† • CX • H
d (g ↥ᵛ)    = d g ↑

-- Paper-V0's words are in operator order, Cliff₃'s in diagram order.
Dʷ : Word (VGen n) → Circuit n
Dʷ [ g ]ʷ  = d g
Dʷ ε       = ε
Dʷ (u • v) = Dʷ v • Dʷ u

D-↑ : (w : Word (VGen n)) → Dʷ (wmap _↥ᵛ w) ≡ Dʷ w ↑
D-↑ [ g ]ʷ  = refl
D-↑ ε       = refl
D-↑ (u • v) = Eq.cong₂ _•_ (D-↑ v) (D-↑ u)

------------------------------------------------------------------------
-- Paper-V0's rules, decoded, hold up to a power of ω

private
  -- A gate on the bottom wire, and the CZ word on the bottom two,
  -- commute with every circuit above them.
  pass : {a b w : Circuit n} → n ⊢ a • w ≈ w • a → n ⊢ b • w ≈ w • b →
         n ⊢ (a • b) • w ≈ w • (a • b)
  pass {a = a} {b} {w} p q = PB.trans PB.assoc (PB.trans (PB.cong PB.refl q)
    (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong p PB.refl) PB.assoc)))

  comm-H : (w : Circuit n) → (₁₊ n) ⊢ H • w ↑ ≈ w ↑ • H
  comm-H w = PB.sym (comm-gate₁-w↑ ⌈ H-gate ⌉ w)

  comm-CZ : (w : Circuit n) → (₂₊ n) ⊢ (H† • CX • H) • w ↑ ↑ ≈ w ↑ ↑ • (H† • CX • H)
  comm-CZ w = pass (pass (comm-H (w ↑)) (pass (comm-H (w ↑)) (comm-H (w ↑))))
                   (pass (PB.sym (comm-gate₂-w↑↑ ⌈ CX-gate ⌉ w)) (comm-H (w ↑)))

  D-srel : {u v : Word (VGen n)} → n VB.SRel, u === v → n ⊢ Dʷ u ≈ω Dʷ v
  D-srel VB.order-S                    = 0 , via DV0-order-S⁼ refl refl
  D-srel VB.order-H                    = 9 , via DV0-order-H⁼ refl refl
  D-srel (VB.M-power zero)             = 3 , via DV0-M-power-0⁼ refl refl
  D-srel (VB.M-power (suc zero))       = 0 , PP.by-assoc _ refl
  D-srel (VB.M-power (suc (suc zero))) = 9 , via DV0-M-power-2⁼ refl refl
  D-srel VB.semi-MR                    = 0 , via DV0-semi-MR⁼ refl refl
  D-srel VB.order-SH                   = 1 , via DV0-order-SH⁼ refl refl
  D-srel VB.comm-HHSHHS                = 0 , via DV0-comm-HHSHHS⁼ refl refl
  D-srel VB.order-CZ                   = 0 , via DV0-order-CZ⁼ refl refl
  D-srel VB.order-Ex                   = 0 , via DV0-order-Ex⁼ refl refl
  D-srel VB.comm-CZ-S↑                 = 0 , via DV0-comm-CZ-S↑⁼ refl refl
  D-srel VB.semi-M↑CZ                  = 0 , via DV0-semi-M↑CZ⁼ refl refl
  D-srel VB.semi-Ex-S↑                 = 0 , via DV0-semi-Ex-S↑⁼ refl refl
  D-srel VB.semi-Ex-H↑                 = 0 , via DV0-semi-Ex-H↑⁼ refl refl
  D-srel VB.blake-c12                  = 0 , via DV0-blake-c12⁼ refl refl
  D-srel VB.yang-baxter                = 0 , via DV0-yang-baxter⁼ refl refl
  D-srel VB.cz-slide                   = 0 , via DV0-cz-slide⁼ refl refl
  D-srel VB.semi-CX↑-CZ↓               = 0 , via DV0-semi-CX↑-CZ↓⁼ refl refl

  -- One wire up.
  up-ω : (u v : Word (VGen n)) → n ⊢ Dʷ u ≈ω Dʷ v →
         (₁₊ n) ⊢ Dʷ (wmap _↥ᵛ u) ≈ω Dʷ (wmap _↥ᵛ v)
  up-ω {n} u v (c , e) = c , (begin
    Dʷ (wmap _↥ᵛ u)          ≡⟨ D-↑ u ⟩
    Dʷ u ↑                   ≈⟨ lemma-cong↑ (Dʷ u) (ωᵏ c • Dʷ v) e ⟩
    ωᵏ c ↑ • Dʷ v ↑          ≈⟨ cong (ωᵏ-↑ c) refl ⟩
    ωᵏ c • Dʷ v ↑            ≡⟨ Eq.cong (ωᵏ c •_) (Eq.sym (D-↑ v)) ⟩
    ωᵏ c • Dʷ (wmap _↥ᵛ v)   ∎)
    where
    open PB ((₁₊ n) VRel,_===_)
    open PP ((₁₊ n) VRel,_===_) using (word-setoid)
    open import Relation.Binary.Reasoning.Setoid word-setoid

  exact : {w v : Circuit n} → n ⊢ w ≈ v → n ⊢ w ≈ω v
  exact e = 0 , PB.trans e (PB.sym PB.left-unit)

  D-rel : {u v : Word (VGen n)} → n V0, u === v → n ⊢ Dʷ u ≈ω Dʷ v
  D-rel (srelᵛ r)                     = D-srel r
  D-rel (cong↑ᵛ {w = u} {v = v} e)    = up-ω u v (D-rel e)
  D-rel (comm₁ᵛ vH g)                 = exact (comm-H (d g))
  D-rel (comm₁ᵛ vS g)                 = exact (PB.sym (comm-gate₁-w↑ ⌈ S-gate ⌉ (d g)))
  D-rel (comm₂ᵛ vCZ g)                = exact (comm-CZ (d g))

  ω-sym : {w v : Circuit n} → n ⊢ w ≈ω v → n ⊢ v ≈ω w
  ω-sym (c , p) = c * 11 , ω-flip c p

  ω-trans : {w v t : Circuit n} → n ⊢ w ≈ω v → n ⊢ v ≈ω t → n ⊢ w ≈ω t
  ω-trans {t = t} (a , p) (b , q) =
    a + b , PB.trans p (PB.trans (PB.cong PB.refl q) (ω-shift a b t))

  -- (the decoding reverses a word)
  ω-cong : {w w' v v' : Circuit n} → n ⊢ w ≈ω w' → n ⊢ v ≈ω v' → n ⊢ v • w ≈ω v' • w'
  ω-cong {w' = w'} {v' = v'} (a , p) (b , q) =
    b + a , PB.trans (PB.cong q p) (ω-pull b a v' w')

D-≈ : {u v : Word (VGen n)} → PB._≈_ (n V0,_===_) u v → n ⊢ Dʷ u ≈ω Dʷ v
D-≈ PB.refl          = exact PB.refl
D-≈ (PB.sym e)       = ω-sym (D-≈ e)
D-≈ (PB.trans e f)   = ω-trans (D-≈ e) (D-≈ f)
D-≈ (PB.cong e f)    = ω-cong (D-≈ e) (D-≈ f)
D-≈ PB.assoc         = exact (PB.sym PB.assoc)
D-≈ PB.left-unit     = exact PB.right-unit
D-≈ PB.right-unit    = exact PB.left-unit
D-≈ (PB.axiom a)     = D-rel a

------------------------------------------------------------------------
-- Lemma 19 with scalars: a circuit is ω^c times the decoding of its
-- encoding

c₀ : Gen n → ℕ
c₀ (gate₀ _) = 1
c₀ (g ↥)     = c₀ g
c₀ _         = 0

cʷ : Circuit n → ℕ
cʷ [ g ]ʷ  = c₀ g
cʷ ε       = 0
cʷ (w • v) = cʷ w + cʷ v

back-gen : (g : Gen n) → n ⊢ [ g ]ʷ ≈ ωᵏ (c₀ g) • Dʷ (E₀ g)
back-gen (gate₀ ⌈ ω-gate ⌉)              = PP.by-assoc _ refl
back-gen (gate₁ ⌈ H-gate ⌉)              = PB.sym PB.left-unit
back-gen (gate₁ ⌈ S-gate ⌉)              = PB.sym PB.left-unit
back-gen {suc (suc n)} (gate₂ ⌈ CX-gate ⌉) = via DCX⁼ refl refl
back-gen {suc (suc n)} (gate₂ swap)        = via (sym⁼ DEx⁼) refl refl
back-gen (gate₃ ⌈ () ⌉)
back-gen {suc n} (g ↥)                   = begin
  [ g ]ʷ ↑                               ≈⟨ lemma-cong↑ [ g ]ʷ (ωᵏ (c₀ g) • Dʷ (E₀ g)) (back-gen g) ⟩
  ωᵏ (c₀ g) ↑ • Dʷ (E₀ g) ↑              ≈⟨ cong (ωᵏ-↑ (c₀ g)) refl ⟩
  ωᵏ (c₀ g) • Dʷ (E₀ g) ↑                ≡⟨ Eq.cong (ωᵏ (c₀ g) •_) (Eq.sym (D-↑ (E₀ g))) ⟩
  ωᵏ (c₀ g) • Dʷ (wmap _↥ᵛ (E₀ g))       ∎
  where
  open PB ((₁₊ n) VRel,_===_)
  open PP ((₁₊ n) VRel,_===_) using (word-setoid)
  open import Relation.Binary.Reasoning.Setoid word-setoid

back : (w : Circuit n) → n ⊢ w ≈ ωᵏ (cʷ w) • Dʷ (E₀ʷ w)
back [ g ]ʷ  = back-gen g
back ε       = PB.sym PB.left-unit
back (w • v) = PB.trans (PB.cong (back w) (back v))
                        (ω-pull (cʷ w) (cʷ v) (Dʷ (E₀ʷ w)) (Dʷ (E₀ʷ v)))

------------------------------------------------------------------------
-- Inverses

inv₀ : Gen n → Circuit n
inv₀ (gate₀ ⌈ ω-gate ⌉)  = ωᵏ 11
inv₀ (gate₁ ⌈ H-gate ⌉)  = H • H • H
inv₀ (gate₁ ⌈ S-gate ⌉)  = S • S
inv₀ (gate₂ ⌈ CX-gate ⌉) = CX • CX
inv₀ (gate₂ swap)        = σ
inv₀ (gate₃ ⌈ () ⌉)
inv₀ (g ↥)               = inv₀ g ↑

invʷ : Circuit n → Circuit n
invʷ [ g ]ʷ  = inv₀ g
invʷ ε       = ε
invʷ (w • v) = invʷ v • invʷ w

inv-r₀ : (g : Gen n) → n ⊢ [ g ]ʷ • inv₀ g ≈ ε
inv-r₀ (gate₀ ⌈ ω-gate ⌉)   = ωᵏ¹²
inv-r₀ (gate₁ ⌈ H-gate ⌉)   = via H⁴⁼ refl refl
inv-r₀ (gate₁ ⌈ S-gate ⌉)   = via S³⁼ refl refl
inv-r₀ (gate₂ ⌈ CX-gate ⌉)  = via QCCC⁼ refl refl
inv-r₀ (gate₂ swap)         = via σσ⁼ refl refl
inv-r₀ (gate₃ ⌈ () ⌉)
inv-r₀ (g ↥)                = lemma-cong↑ ([ g ]ʷ • inv₀ g) ε (inv-r₀ g)

inv-r : (w : Circuit n) → n ⊢ w • invʷ w ≈ ε
inv-r [ g ]ʷ  = inv-r₀ g
inv-r ε       = PB.left-unit
inv-r (w • v) = PB.trans PB.assoc (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
  (PB.trans (PB.cong (inv-r v) PB.refl) PB.left-unit))) (inv-r w))

------------------------------------------------------------------------
-- A power of ω with the identity's matrix is ε

private
  module X = Circuits Sem.val
  module XE = X.Exact

  δ₁-refl : (a : Fin 3) → δ₁ a a ≡ 1q
  δ₁-refl zero          = refl
  δ₁-refl (suc zero)    = refl
  δ₁-refl (suc (suc zero)) = refl

  δv-refl : (z : Digits n) → δv z z ≡ 1q
  δv-refl []      = refl
  δv-refl (a ∷ z) = Eq.trans (Eq.cong₂ _*ᵠ_ (δ₁-refl a) (δv-refl z)) (*-identityˡ 1q)

  scal-⊙ : (a b : Q) → (scal {n} a ⊙ scal b) ≐ scal (a *ᵠ b)
  scal-⊙ a b u v = begin
    Σv (λ z → (a *ᵠ δv u z) *ᵠ (b *ᵠ δv z v))   ≡⟨ Σ-cong (λ z → *-assoc a (δv u z) (b *ᵠ δv z v)) ⟩
    Σv (λ z → a *ᵠ (δv u z *ᵠ (b *ᵠ δv z v)))   ≡⟨ Σ-scaleˡ a (λ z → δv u z *ᵠ (b *ᵠ δv z v)) ⟩
    a *ᵠ Σv (λ z → δv u z *ᵠ (b *ᵠ δv z v))     ≡⟨ Eq.cong (a *ᵠ_) (Σ-δˡ u (λ z → b *ᵠ δv z v)) ⟩
    a *ᵠ (b *ᵠ δv u v)                          ≡⟨ Eq.sym (*-assoc a b (δv u v)) ⟩
    (a *ᵠ b) *ᵠ δv u v                          ∎
    where
    open Eq.≡-Reasoning

  -- ωᵏ reads as xᵏ times the identity, with no power of 1/√3.
  ⟦ωᵏ⟧₁ : (k : ℕ) → proj₁ (Sem.⟦ ωᵏ {n} k ⟧) ≡ 0
  ⟦ωᵏ⟧₁ zero    = refl
  ⟦ωᵏ⟧₁ (suc k) = ⟦ωᵏ⟧₁ k

  ⟦ωᵏ⟧₂ : (k : ℕ) → ix (proj₂ (Sem.⟦ ωᵏ {n} k ⟧)) ≐ scal (x ^ k)
  ⟦ωᵏ⟧₂ zero    u v = Eq.trans (ix-id u v) (Eq.sym (*-identityˡ (δv u v)))
  ⟦ωᵏ⟧₂ (suc k) u v = begin
    ix (proj₂ Sem.⟦ ω • ωᵏ k ⟧) u v                       ≡⟨ ix-mul (proj₂ Sem.⟦ ωᵏ k ⟧) _ u v ⟩
    (ix (proj₂ Sem.⟦ ωᵏ k ⟧) ⊙ ix (proj₂ Sem.⟦ ω ⟧)) u v  ≡⟨ Σ-cong (λ z → Eq.cong₂ _*ᵠ_ (⟦ωᵏ⟧₂ k u z)
                                                                      (ix-scalM x z v)) ⟩
    (scal (x ^ k) ⊙ scal x) u v                           ≡⟨ scal-⊙ (x ^ k) x u v ⟩
    (x ^ k *ᵠ x) *ᵠ δv u v                                ≡⟨ Eq.cong (_*ᵠ δv u v) (*-comm (x ^ k) x) ⟩
    (x *ᵠ x ^ k) *ᵠ δv u v                                ∎
    where open Eq.≡-Reasoning

  -- ζᵏ = 1 only for k a multiple of 12.
  x^j : (j : ℕ) → j < 12 → x ^ j ≡ 1q → j ≡ 0
  x^j 0 _ _ = refl
  x^j 1 _ ()
  x^j 2 _ ()
  x^j 3 _ ()
  x^j 4 _ ()
  x^j 5 _ ()
  x^j 6 _ ()
  x^j 7 _ ()
  x^j 8 _ ()
  x^j 9 _ ()
  x^j 10 _ ()
  x^j 11 _ ()
  x^j (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))))
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))))

  zs : (n : ℕ) → Digits n
  zs n = replicate n zero

  ωᵏ-trivial : (k : ℕ) → Sem.⟦ ωᵏ {n} k ⟧ Sem.≈ εs → n ⊢ ωᵏ k ≈ ε
  ωᵏ-trivial {n} k (XE.phased _ refl agree) =
    PB.trans (ωᵏ-mod k) (Eq.subst (λ j → n ⊢ ωᵏ j ≈ ε) (Eq.sym j≡0) PB.refl)
    where
    open Eq.≡-Reasoning
    xk : x ^ k ≡ 1q
    xk = begin
      x ^ k                                       ≡⟨ Eq.sym (*-identityʳ (x ^ k)) ⟩
      x ^ k *ᵠ 1q                                 ≡⟨ Eq.cong (x ^ k *ᵠ_) (Eq.sym (δv-refl (zs n))) ⟩
      x ^ k *ᵠ δv (zs n) (zs n)                   ≡⟨ Eq.sym (⟦ωᵏ⟧₂ k (zs n) (zs n)) ⟩
      ix (proj₂ Sem.⟦ ωᵏ k ⟧) (zs n) (zs n)       ≡⟨ Eq.sym (*-identityˡ _) ⟩
      1q *ᵠ ix (proj₂ Sem.⟦ ωᵏ k ⟧) (zs n) (zs n) ≡⟨ agree (zs n) (zs n) ⟩
      (1q *ᵠ √3 ^ proj₁ Sem.⟦ ωᵏ {n} k ⟧) *ᵠ ix (proj₂ (εs {n})) (zs n) (zs n)
        ≡⟨ Eq.cong₂ (λ h e → (1q *ᵠ √3 ^ h) *ᵠ e) (⟦ωᵏ⟧₁ k)
                    (Eq.trans (ix-id (zs n) (zs n)) (δv-refl (zs n))) ⟩
      (1q *ᵠ √3 ^ 0) *ᵠ 1q                        ≡⟨⟩
      1q                                          ∎
    j≡0 : k % 12 ≡ 0
    j≡0 = x^j (k % 12) (m%n<n k 12) (Eq.trans (Eq.sym (x^-mod k)) xk)

  -- A circuit's matrix up to ωᵏ is its own only when ωᵏ is ε.
  scalar : (k : ℕ) (v : Circuit n) → Sem.⟦ v ⟧ Sem.≈ Sem.⟦ ωᵏ k • v ⟧ → n ⊢ ωᵏ k ≈ ε
  scalar {n} k v h = ωᵏ-trivial k
    (XE.≈-trans {s₁ = Sem.⟦ ωᵏ k ⟧} {Sem.⟦ (ωᵏ k • v) • invʷ v ⟧} {εs}
      (Sem.sound padded)
      (XE.≈-trans {s₁ = Sem.⟦ (ωᵏ k • v) • invʷ v ⟧} {Sem.⟦ v • invʷ v ⟧} {εs}
        (XE.∙-cong {s₁ = Sem.⟦ ωᵏ k • v ⟧} {Sem.⟦ v ⟧} {Sem.⟦ invʷ v ⟧} {Sem.⟦ invʷ v ⟧}
          (XE.≈-sym {s = Sem.⟦ v ⟧} {Sem.⟦ ωᵏ k • v ⟧} h) (XE.≈-refl {s = Sem.⟦ invʷ v ⟧}))
        (Sem.sound (inv-r v))))
    where
    padded : n ⊢ ωᵏ k ≈ (ωᵏ k • v) • invʷ v
    padded = PB.trans (PB.sym PB.right-unit) (PB.trans (PB.cong PB.refl (PB.sym (inv-r v))) (PB.sym PB.assoc))

------------------------------------------------------------------------
-- Completeness

complete : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
complete {n} {w} {v} e = PB.trans up-to (PB.trans (PB.cong ω-trivial PB.refl) PB.left-unit)
  where
  a = cʷ w
  b = cʷ v
  D = D-≈ (bridge {w = w} {v = v} e)
  c = proj₁ D
  k = a + (c + b * 11)

  up-to : n ⊢ w ≈ ωᵏ k • v
  up-to = PB.trans (back w) (PB.trans (PB.cong PB.refl (proj₂ D))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (ω-flip b (back v))))
    (PB.trans (PB.cong PB.refl (ω-shift c (b * 11) v)) (ω-shift a (c + b * 11) v))))

  ω-trivial : n ⊢ ωᵏ k ≈ ε
  ω-trivial = scalar k v
    (XE.≈-trans {s₁ = Sem.⟦ v ⟧} {Sem.⟦ w ⟧} {Sem.⟦ ωᵏ k • v ⟧}
      (XE.≈-sym {s = Sem.⟦ w ⟧} {Sem.⟦ v ⟧} e) (Sem.sound up-to))

-- Cliff₃ is sound and complete at every width.
sound-complete : {w v : Circuit n} → (n ⊢ w ≈ v) ⇔ (Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧)
sound-complete = mk⇔ Sem.sound complete
